# -*- coding: utf-8 -*-
"""
大数分解可视化工具（多进程并行版，纯 Python 标准库，界面为 tkinter）

功能
====
1. 输入一个很大的正整数 N（支持 10^100、2^64、1e50 写法或直接粘贴）。
2. 对每个数量级 10^k（k = 0,1,2,… 直到 N 的数量级），取该数量级的前三个数
   10^k、10^k+1、10^k+2（最后一组不超过 N），按所选模式处理：
   · 完整质因数分解：分解成所有质因数之积；
   · 仅分解为两个数相乘：找到一个非平凡因子 d，给出 n = d × (n/d)，即可证明 n 是合数。
3. 大数一律缩写显示：10^n、10^n+d 或 a.bcd×10^n，避免一长串 0。
4. 本身是质数的数用红色标出；限时内未能完全分解 / 被跳过的用橙色标出。
5. 多进程并行：按 CPU 核数开计算进程（可调），结果仍按数量级顺序显示。
6. 限时可选“不限时”；运行中可 暂停/继续、跳过当前、停止；
   单个数计算超过 2 秒后，会持续打印中间过程（试除→素性检测→p-1→rho 各阶段）。
7. 界面下方实时显示电脑基本信息（CPU 型号/线程数、整机 CPU 占用、内存）和
   本程序占用（进程数、CPU 折合核数、内存）。

用法
====
python factor_gui.py             # 打开界面
python factor_gui.py --demo      # 打开界面并自动演示 N = 10^12
python factor_gui.py --selftest  # 命令行自检（含多进程流水线测试，不开界面）
"""

import math
import multiprocessing
import os
import platform
import queue as queue_mod
import random
import re
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext

# ------------------------------------------------------------------ 参数

SMALL_PRIME_LIMIT = 100_000   # 试除用素数表上限
MR_MAX_BITS = 8_000           # 超过该二进制位数不做 Miller-Rabin（单次幂运算太慢且不可中断）
PM1_MAX_BITS = 2_500          # 超过该位数不做 Pollard p-1
RHO_MAX_BITS = 8_000          # 超过该位数不做 Pollard rho
PM1_B1 = 50_000               # Pollard p-1 第一阶段界限
MAX_DIGITS = 200_000          # 允许输入的最大十进制位数

try:
    sys.set_int_max_str_digits(2_000_000)   # Python 3.11+ 默认 int/str 限制 4300 位
except AttributeError:
    pass


class FactorTimeout(Exception):
    """单个数在限时内未能完成。args 含部分结果"""


class StopRequested(Exception):
    """用户点击了「停止」"""


class SkipRequested(Exception):
    """用户点击了「跳过当前」"""


# ------------------------------------------------------------------ 数学核心

_PRIMES = None


def get_primes():
    """惰性生成 10 万以内的素数表（每个计算进程各自建一次，约几十毫秒）。"""
    global _PRIMES
    if _PRIMES is None:
        n = SMALL_PRIME_LIMIT
        sieve = bytearray(b"\x01") * (n + 1)
        sieve[0] = sieve[1] = 0
        i = 2
        while i * i <= n:
            if sieve[i]:
                sieve[i * i:: i] = b"\x00" * ((n - i * i) // i + 1)
            i += 1
        _PRIMES = [j for j, v in enumerate(sieve) if v]
    return _PRIMES


def _pm1_prime_count():
    return sum(1 for p in get_primes() if p <= PM1_B1)


class Ctl:
    """协同取消（停止/跳过/限时）+ 慢任务进度上报。"""
    __slots__ = ("stop_event", "skip_event", "deadline", "prog", "seq", "t0", "last_note")

    def __init__(self, stop_event=None, skip_event=None, deadline=None, prog=None, seq=0):
        self.stop_event = stop_event
        self.skip_event = skip_event
        self.deadline = deadline
        self.prog = prog            # mp.Queue；None 表示不上报进度（如自检）
        self.seq = seq
        self.t0 = time.perf_counter()
        self.last_note = 0.0

    def elapsed(self):
        return time.perf_counter() - self.t0

    def check(self):
        if self.skip_event is not None and self.skip_event.is_set():
            raise SkipRequested()
        if self.stop_event is not None and self.stop_event.is_set():
            raise StopRequested()
        if self.deadline is not None and time.perf_counter() >= self.deadline:
            raise FactorTimeout()

    def note(self, text):
        """中间过程：单个任务运行 2 秒后才开始上报，且最多每秒一条。"""
        if self.prog is None:
            return
        now = time.perf_counter()
        if now - self.t0 < 2.0 or now - self.last_note < 1.0:
            return
        self.last_note = now
        try:
            self.prog.put(("prog", self.seq, round(now - self.t0, 1), text))
        except Exception:
            pass


def is_prime(n, ctl=None):
    """Miller-Rabin 素性检测。True=素数，False=合数，None=数太大未判定。

    n < 3.3e24 用固定 12 个底数，结果确定性正确；更大的数按位数减少底数
    以保证单次幂运算不会长时间无响应，错误概率约 4^-底数数。
    """
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    if n < 41 * 41:
        return True
    r = math.isqrt(n)
    if r * r == n:
        return False
    if n.bit_length() > MR_MAX_BITS:
        return None
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    if n < 3317044064679887385961981:
        bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    else:
        bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] + [
            random.randrange(2, n - 1) for _ in range(24)
        ]
    nb = max(3, min(len(bases), 24000 // n.bit_length()))
    bases = bases[:nb]
    for bi, a in enumerate(bases, 1):
        if ctl is not None:
            ctl.check()
            tb = time.perf_counter()
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            pass
        else:
            for _ in range(s - 1):
                x = x * x % n
                if x == n - 1:
                    break
            else:
                return False
        if ctl is not None and bi < len(bases):
            eta = (time.perf_counter() - tb) * (len(bases) - bi)
            ctl.note(f"素性检测 Miller-Rabin：底数 {bi}/{len(bases)}（预计还需 ~{eta:.1f} s）")
    return True


def pollard_pm1(n, ctl):
    """Pollard p-1 第一阶段；找到非平凡因子则返回，否则 None。"""
    total = _pm1_prime_count()
    a = 2
    for i, p in enumerate(get_primes(), 1):
        if p > PM1_B1:
            break
        pk = p
        while pk * p <= PM1_B1:
            pk *= p
        a = pow(a, pk, n)
        if ctl is not None and i % 512 == 0:
            ctl.check()
            ctl.note(f"Pollard p-1 阶段：{i}/{total} 个素数幂")
    g = math.gcd(a - 1, n)
    return g if 1 < g < n else None


def pollard_brent(n, ctl):
    """Pollard rho（Brent 变体），返回 n 的一个非平凡因子。"""
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    steps = 0
    restarts = 0
    while True:
        if ctl is not None:
            ctl.check()
        restarts += 1
        y = random.randrange(1, n - 1)
        c = random.randrange(1, n - 1)
        m = 128
        g = r = q = 1
        x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                steps += min(m, r - k)
                g = math.gcd(q, n)
                k += m
                if ctl is not None:
                    ctl.check()
                    rate = steps / max(ctl.elapsed(), 1e-9)
                    ctl.note(f"Pollard rho：第 {restarts} 轮随机重启，累计 {steps} 步"
                             f"（约 {rate / 1e4:.0f} 万步/秒）——随机算法，剩余时间无法可靠预估")
            r <<= 1
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
                if ctl is not None:
                    ctl.check()
        if g != n:
            return g


def factorize(n, ctl):
    """完整质因数分解。正常返回 (因子 dict{素数: 次数}, 未分解剩余 list)。

    限时/停止/跳过时抛对应异常，args = (已分解因子 dict, 剩余未分解 list)。
    """
    factors = {}
    work = [n]
    hard = []
    cur = None
    try:
        while work:
            m = work.pop()
            cur = m
            if ctl is not None:
                ctl.check()
            if m == 1:
                cur = None
                continue
            for p in get_primes():
                if p * p > m:
                    break
                while m % p == 0:
                    factors[p] = factors.get(p, 0) + 1
                    m //= p
            cur = m
            if m == 1:
                cur = None
                continue
            if ctl is not None:
                ctl.check()
                ctl.note(f"试除完成，剩余 {len(str(m))} 位，转入素性检测/随机算法")
            pr = is_prime(m, ctl)
            if pr is True:
                factors[m] = factors.get(m, 0) + 1
                cur = None
                continue
            if pr is None or m.bit_length() > RHO_MAX_BITS:
                hard.append(m)              # 位数过大，不做进一步分解
                cur = None
                continue
            d = None
            if m.bit_length() <= PM1_MAX_BITS:
                d = pollard_pm1(m, ctl)
            if d is None:
                d = pollard_brent(m, ctl)
            work.append(d)
            work.append(m // d)
            cur = None
    except (FactorTimeout, StopRequested, SkipRequested) as e:
        rest = [w for w in work if w > 1] + hard
        if cur is not None and cur > 1:
            rest.append(cur)
        e.args = (dict(factors), rest)
        raise
    return factors, hard


def factorize_two(n, ctl):
    """仅找一个非平凡因子：返回 (d, n//d) 证明合数；n 是质数返回 None。

    无法完成时抛 FactorTimeout（args=(已找到的 d 或 None,)）。
    """
    if n % 2 == 0:
        return (2, n // 2)
    for p in get_primes():
        if p * p > n:
            break
        if n % p == 0:
            return (p, n // p)
    pr = is_prime(n, ctl)
    if pr is True:
        return None
    if ctl is not None:
        ctl.check()
        ctl.note("小因子试除完成，转入随机算法找任一因子")
    try:
        if n.bit_length() <= PM1_MAX_BITS:
            d = pollard_pm1(n, ctl)
            if d:
                return (d, n // d)
        if n.bit_length() > RHO_MAX_BITS:
            raise FactorTimeout((None,))
        d = pollard_brent(n, ctl)
        return (d, n // d)
    except FactorTimeout as e:
        if not e.args:
            e.args = (None,)
        raise


# ------------------------------------------------------------------ 显示辅助

def pretty_num(x, limit=18):
    """大数缩写：10^n / 10^n+d / a.bcd×10^n；短数直接显示。

    ≥10 位的数若为 10 的幂或 10^n 加小偏移，一律缩写（无论多长）；
    其余 ≤18 位照原样显示，更长的用 7 位有效数字的科学计数法。
    """
    s = str(x)
    if len(s) >= 10:
        if s[0] == "1" and set(s[1:]) <= {"0"}:
            return f"10^{len(s) - 1}"
        k = len(s) - 1
        d = x - 10 ** k
        if 0 <= d < 10 ** 7:
            return f"10^{k}+{d}"
        if len(s) > limit:
            return f"{s[0]}.{s[1:7]}×10^{k}"
    return s


def fmt_factors(factors):
    parts = []
    for p in sorted(factors):
        e = factors[p]
        parts.append(pretty_num(p) if e == 1 else f"{pretty_num(p)}^{e}")
    return " × ".join(parts)


def fmt_time(t):
    if t >= 1:
        return f"{t:.2f} s"
    if t >= 1e-3:
        return f"{t * 1e3:.2f} ms"
    return f"{t * 1e6:.1f} µs"


def render_result(num, kind, a, b, dt, pad):
    """把单个数的计算结果渲染为输出行。(line, tag)"""
    t = f"用时 {fmt_time(dt)}"
    nd = pretty_num(num, 60)
    if kind == "unit":
        return f"  {nd} = 1（既不是质数也不是合数）    {t}\n", None
    if kind == "prime":
        return f"  {nd} = 质数（本身不可再分解）    {t}\n", "prime"
    if kind == "two":
        return f"  {nd} = {pretty_num(a)} × {pretty_num(b)}（两数相乘，已证明是合数）    {t}\n", None
    if kind == "twofail":
        return f"  {nd} = ？【限时内未找到非平凡因子：既未能证明是合数，也未确认为质数】    {t}\n", "hard"
    if kind in ("timeout", "stopped", "skipped", "fullhard"):
        note = {"timeout": "【限时内未能完全分解】",
                "stopped": "【已停止，未完全分解】",
                "skipped": "【已跳过（用户中止）】",
                "fullhard": "【位数过大，仅试除到 10^5，未能完全分解】"}[kind]
        base = fmt_factors(a) if a else ""
        if b:
            rp = " × ".join(f"{pretty_num(r, 44)}（{len(str(r))}位）" for r in b)
            body = f"{base} × {rp}{note}" if base else rp + note
        else:
            body = (base + note) if base else note
        return f"  {nd} = {body}    {t}\n", "hard"
    if kind == "error":
        return f"  {nd} = 【计算出错】{a}    {t}\n", "hard"
    return f"  {nd} = {fmt_factors(a)}    {t}\n", None


# ------------------------------------------------------------------ 任务生成

def count_numbers(N):
    """每个数量级取前三个数（不超过 N），总共多少个数。"""
    c = 0
    p = 1
    while p <= N:
        c += 3 if p + 2 <= N else (2 if p + 1 <= N else 1)
        p *= 10
    return c


def build_tasks(N):
    """（自检用）与 iter_display_items 等价的任务列表。"""
    tasks = []
    p = 1
    while p <= N:
        tasks.append([x for x in (p, p + 1, p + 2) if x <= N])
        p *= 10
    return tasks


def iter_display_items(N):
    """按顺序产出显示项：("header", k, nums, pad) 和 ("num", x, pad)。"""
    p = 1
    k = 0
    while p <= N:
        nums = [x for x in (p, p + 1, p + 2) if x <= N]
        pad = min(max(len(pretty_num(x, 60)) for x in nums), 60)
        yield ("header", k, nums, pad)
        for x in nums:
            yield ("num", x, pad)
        p *= 10
        k += 1


def parse_input(text):
    s = str(text).strip()
    for ch in (",", " ", "_", "\t", "，", "、", "　"):
        s = s.replace(ch, "")
    if not s:
        raise ValueError("请输入一个正整数（支持 10^100、1e50 或直接粘贴数字）")
    n = None
    m = re.fullmatch(r"(\d+)\^(\d+)", s)
    if m:
        base, exp = int(m.group(1)), int(m.group(2))
        if base < 2 or exp < 1:
            raise ValueError("a^b 形式要求 a ≥ 2 且 b ≥ 1")
        if exp > 100_000 or len(m.group(1)) * exp > MAX_DIGITS:
            raise ValueError("a^b 的结果超过 20 万位，请换个小一点的数")
        n = base ** exp
    else:
        m = re.fullmatch(r"(\d+)[eE](\d+)", s)
        if m:
            if len(m.group(1)) + int(m.group(2)) > MAX_DIGITS:
                raise ValueError("数值超过 20 万位，请换个小一点的数")
            n = int(m.group(1)) * (10 ** int(m.group(2)))
        elif s.isdigit():
            n = int(s)
        else:
            raise ValueError("无法识别的格式；支持：12345、10^100、2^64、1e50")
    if n < 1:
        raise ValueError("请输入 ≥ 1 的整数")
    if len(str(n)) > MAX_DIGITS:
        raise ValueError("数值超过 20 万位，请换个小一点的数")
    return n


# ------------------------------------------------------------------ 多进程计算

def _do_task(seq, num, limit, mode, stop_event, skip_event, result_q):
    """在计算进程里处理一个数，返回结构化结果（也可中途发进度消息）。"""
    deadline = None if not limit else time.perf_counter() + limit
    ctl = Ctl(stop_event, skip_event, deadline, prog=result_q, seq=seq)
    t1 = time.perf_counter()
    try:
        if num == 1:
            return ("result", seq, "unit", None, None, 0.0)
        if mode == "two":
            r = factorize_two(num, ctl)
            dt = time.perf_counter() - t1
            if r is None:
                return ("result", seq, "prime", None, None, dt)
            return ("result", seq, "two", r[0], r[1], dt)
        factors, hard = factorize(num, ctl)
        dt = time.perf_counter() - t1
        return ("result", seq, "fullhard" if hard else "full", factors, hard, dt)
    except FactorTimeout as e:
        dt = time.perf_counter() - t1
        if mode == "two":
            d = e.args[0] if e.args else None
            return ("result", seq, "twofail", d, None, dt)
        f, r = e.args if len(e.args) == 2 else ({}, [num])
        return ("result", seq, "timeout", f, r, dt)
    except SkipRequested:
        return ("result", seq, "skipped", None, None, time.perf_counter() - t1)
    except StopRequested as e:
        dt = time.perf_counter() - t1
        if mode == "two":
            return ("result", seq, "stopped", None, None, dt)
        f, r = e.args if len(e.args) == 2 else ({}, [num])
        return ("result", seq, "stopped", f, r, dt)
    except Exception as e:
        return ("result", seq, "error", f"{type(e).__name__}: {e}", None,
                time.perf_counter() - t1)


def _pool_worker(task_q, result_q, stop_event, skip_event):
    """计算进程主循环：取任务 → 计算 → 回传；收到 None 哨兵退出。"""
    while True:
        try:
            task = task_q.get()
        except (EOFError, OSError):
            return
        if task is None:
            return
        seq, num, limit, mode = task
        try:
            res = _do_task(seq, num, limit, mode, stop_event, skip_event, result_q)
        except Exception as e:
            res = ("result", seq, "error", repr(e), None, 0.0)
        try:
            result_q.put(res)
        except Exception:
            return


class PoolRunner:
    """多进程分解流水线：任务按数量级顺序生成，结果按原顺序回传给界面。

    out_q 消息：
      ("slot", seq, text, tag)            按顺序显示的行（含数量级标题）
      ("progline", text)                  慢任务中间过程
      ("status", text) / ("outstanding", n)
      ("summary", text, status_text)      结束汇总
      ("error", text)
    """

    def __init__(self, N, limit, mode, workers, out_q):
        self.N = N
        self.limit = limit            # None = 不限时
        self.mode = mode              # "full" / "two"
        self.workers = max(1, int(workers))
        self.out_q = out_q
        self.pids = []
        self._procs = []
        self._task_q = None
        self._result_q = None
        self._stop_event = None
        self._skip_event = None
        self._stop_flag = False
        self._paused = False
        self._skip_wait = False
        self._exhausted = False
        self._finished = False
        self._outstanding = {}        # seq -> (num, pretty, pad, t_submit)
        self._pending_item = None
        self._seq = 0
        self._items = None
        self._stats = {"n": 0, "prime": 0, "partial": 0, "fact": 0.0}
        self._done = 0
        self._total = count_numbers(N)
        self._t0 = time.perf_counter()

    def start(self):
        ctx = multiprocessing.get_context("spawn")
        self._task_q = ctx.Queue()
        self._result_q = ctx.Queue()
        self._stop_event = ctx.Event()
        self._skip_event = ctx.Event()
        for _ in range(self.workers):
            p = ctx.Process(target=_pool_worker,
                            args=(self._task_q, self._result_q,
                                  self._stop_event, self._skip_event),
                            daemon=True)
            p.start()
            self._procs.append(p)
            self.pids.append(p.pid)
        self._items = iter_display_items(self.N)
        threading.Thread(target=self._feeder_loop, daemon=True).start()

    def pause(self):
        self._paused = True

    def resume(self):
        self._paused = False

    def skip_current(self):
        if self._outstanding:
            self._skip_event.set()
            self._skip_wait = True

    def stop(self):
        self._stop_flag = True
        self._stop_event.set()

    def alive_pids(self):
        """仍然存活的计算进程 pid（供资源监控用）。"""
        return [p.pid for p in self._procs if p.exitcode is None]

    def close(self):
        """立即终止（仅用于退出程序）。"""
        self._stop_flag = True
        if self._stop_event is not None:
            self._stop_event.set()
        for p in self._procs:
            if p.is_alive():
                try:
                    p.terminate()
                except Exception:
                    pass

    # ---------------- 内部 ----------------

    def _header_text(self, item):
        _, k, nums, _pad = item
        lo = nums[0]
        upper = f"10^{k + 1}-1" if k >= 1 else "9"
        if self.N < lo * 10:                      # 最后一个不完整的数量级
            upper = pretty_num(self.N, 30)
        return ("\n" + "─" * 12 + f" 数量级 10^{k}（{pretty_num(lo, 30)} ~ {upper}）"
                + "─" * 12 + "\n")

    def _refill(self):
        while not self._stop_flag and not self._paused \
                and len(self._outstanding) < self.workers and not self._exhausted:
            if self._pending_item is None:
                try:
                    self._pending_item = next(self._items)
                except StopIteration:
                    self._exhausted = True
                    return
            item = self._pending_item
            if item[0] == "header":
                self._pending_item = None
                self.out_q.put(("slot", self._seq, self._header_text(item), "group"))
                self._seq += 1
                continue
            _, num, pad = item
            seq = self._seq
            self._task_q.put((seq, num, self.limit, self.mode))
            self._outstanding[seq] = (num, pretty_num(num, 46), pad, time.perf_counter())
            self._seq += 1
            self._pending_item = None

    def _on_result(self, msg):
        _, seq, kind, a, b, dt = msg
        info = self._outstanding.pop(seq, None)
        if info is None:
            return
        num, _pretty, pad, _t = info
        line, tag = render_result(num, kind, a, b, dt, pad)
        self._done += 1
        self._stats["n"] += 1
        self._stats["fact"] += dt
        if tag == "prime":
            self._stats["prime"] += 1
        if kind in ("timeout", "stopped", "skipped", "fullhard", "twofail", "error"):
            self._stats["partial"] += 1
        self.out_q.put(("slot", seq, line, tag))
        if self._skip_wait and not self._outstanding:
            self._skip_event.clear()
            self._skip_wait = False

    def _post_status(self):
        now = time.perf_counter()
        infl = "｜".join(f"{pretty}（{now - t:.1f}s）"
                         for _seq, (_num, pretty, _p, t) in
                         sorted(self._outstanding.items())[:6])
        txt = (f"已完成 {self._done}/{self._total}"
               + (f" · 进行中：{infl}" if infl else "")
               + (" · 已暂停" if self._paused else "")
               + (" · 正在停止…" if self._stop_flag else "")
               + (" · 已请求跳过当前…" if self._skip_wait else ""))
        self.out_q.put(("status", txt))
        self.out_q.put(("outstanding", len(self._outstanding)))

    def _feeder_loop(self):
        try:
            last_status = 0.0
            while True:
                while True:                      # 1) 收结果/进度
                    try:
                        msg = self._result_q.get(timeout=0.02)
                    except queue_mod.Empty:
                        break
                    except (OSError, ValueError):
                        break
                    if msg[0] == "prog":
                        _, seq, elapsed, text = msg
                        info = self._outstanding.get(seq)
                        if info:
                            self.out_q.put(("progline",
                                            f"    [运行中] {info[1]} 已 {elapsed}s：{text}"))
                    elif msg[0] == "result":
                        self._on_result(msg)
                self._refill()                   # 2) 填充任务
                now = time.perf_counter()        # 3) 状态
                if now - last_status >= 0.4:
                    last_status = now
                    self._post_status()
                if self._exhausted and not self._outstanding \
                        and self._pending_item is None:
                    break                        # 正常结束
                if self._stop_flag and not self._outstanding:
                    break                        # 用户停止
            self._shutdown()
        except Exception as e:
            try:
                self.out_q.put(("error", f"流水线出错：{type(e).__name__}: {e}"))
            except Exception:
                pass

    def _shutdown(self):
        for _ in self._procs:
            try:
                self._task_q.put_nowait(None)
            except Exception:
                pass
        deadline = time.perf_counter() + 10
        for p in self._procs:
            p.join(timeout=max(0.1, deadline - time.perf_counter()))
        for p in self._procs:
            if p.is_alive():
                try:
                    p.terminate()
                except Exception:
                    pass
        if self._finished:
            return
        self._finished = True
        wall = time.perf_counter() - self._t0
        s = self._stats
        mode_txt = "完整质因数分解" if self.mode == "full" else "仅分解为两数相乘（证合数）"
        limit_txt = "不限时" if not self.limit else f"每数限时 {self.limit}s"
        head = "已停止" if self._stop_flag else "全部完成"
        summary = (
            "\n" + "═" * 78 + "\n"
            + f"{head}｜模式：{mode_txt}｜{self.workers} 进程｜{limit_txt}\n"
            + f"共处理 {s['n']} 个数 · 质数 {s['prime']} 个 · 未完全分解/跳过 {s['partial']} 个\n"
            + f"分解总计用时：{fmt_time(s['fact'])}（从开始到结束共 {fmt_time(wall)}）\n")
        status = (f"{head} · 共 {s['n']} 个数 · 质数 {s['prime']} 个"
                  + (f" · 未完全分解/跳过 {s['partial']} 个" if s["partial"] else "")
                  + f" · 分解总计用时 {fmt_time(s['fact'])}")
        self.out_q.put(("summary", summary, status))


# ------------------------------------------------------------------ 系统信息 / 资源占用

_CPU_NAME = None


def get_cpu_name():
    global _CPU_NAME
    if _CPU_NAME is None:
        name = ""
        try:
            import winreg
            with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,
                                r"HARDWARE\DESCRIPTION\System\CentralProcessor\0") as k:
                name = winreg.QueryValueEx(k, "ProcessorNameString")[0].strip()
        except Exception:
            name = platform.processor() or ""
        _CPU_NAME = name or "未知 CPU"
    return _CPU_NAME


def _ram_info():
    try:
        import ctypes

        class MEMORYSTATUSEX(ctypes.Structure):
            _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong),
                        ("ullTotalPhys", ctypes.c_ulonglong),
                        ("ullAvailPhys", ctypes.c_ulonglong),
                        ("ullTotalPageFile", ctypes.c_ulonglong),
                        ("ullAvailPageFile", ctypes.c_ulonglong),
                        ("ullTotalVirtual", ctypes.c_ulonglong),
                        ("ullAvailVirtual", ctypes.c_ulonglong),
                        ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]

        st = MEMORYSTATUSEX()
        st.dwLength = ctypes.sizeof(MEMORYSTATUSEX)
        if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(st)):
            return st.dwMemoryLoad, st.ullTotalPhys, st.ullAvailPhys
    except Exception:
        pass
    return None


def _system_times():
    try:
        import ctypes
        idle = ctypes.c_ulonglong()
        kern = ctypes.c_ulonglong()
        user = ctypes.c_ulonglong()
        if ctypes.windll.kernel32.GetSystemTimes(ctypes.byref(idle), ctypes.byref(kern),
                                                 ctypes.byref(user)):
            return (idle.value, kern.value, user.value)
    except Exception:
        pass
    return None


def _proc_cpu_time(pid):
    """进程累计 CPU 时间（秒，含所有线程）；失败返回 None。"""
    try:
        import ctypes
        k32 = ctypes.windll.kernel32
        h = k32.OpenProcess(0x1000, False, pid)   # PROCESS_QUERY_LIMITED_INFORMATION
        if not h:
            return None
        try:
            ct, et, kt, ut = (ctypes.c_ulonglong() for _ in range(4))
            if k32.GetProcessTimes(h, ctypes.byref(ct), ctypes.byref(et),
                                   ctypes.byref(kt), ctypes.byref(ut)):
                return (kt.value + ut.value) / 1e7
            return None
        finally:
            k32.CloseHandle(h)
    except Exception:
        return None


def _proc_workingset(pid):
    """进程工作集内存（字节）；失败返回 None。"""
    try:
        import ctypes

        class PMC(ctypes.Structure):
            _fields_ = [("cb", ctypes.c_ulong), ("PageFaultCount", ctypes.c_ulong),
                        ("PeakWorkingSetSize", ctypes.c_size_t),
                        ("WorkingSetSize", ctypes.c_size_t),
                        ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                        ("QuotaPagedPoolUsage", ctypes.c_size_t),
                        ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                        ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                        ("PagefileUsage", ctypes.c_size_t),
                        ("PeakPagefileUsage", ctypes.c_size_t)]

        k32 = ctypes.windll.kernel32
        h = k32.OpenProcess(0x1000, False, pid)
        if not h:
            return None
        try:
            pmc = PMC()
            pmc.cb = ctypes.sizeof(PMC)
            if ctypes.windll.psapi.GetProcessMemoryInfo(h, ctypes.byref(pmc), pmc.cb):
                return pmc.WorkingSetSize
            return None
        finally:
            k32.CloseHandle(h)
    except Exception:
        return None


def _fmt_bytes(n):
    if n >= 1024 ** 3:
        return f"{n / 1024 ** 3:.1f} GB"
    if n >= 1024 ** 2:
        return f"{n / 1024 ** 2:.0f} MB"
    return f"{n / 1024:.0f} KB"


# ------------------------------------------------------------------ 界面

TAGS = {
    "group": {"foreground": "#1a5fa8", "font": ("Consolas", 10, "bold")},
    "prime": {"foreground": "#c0392b"},
    "hard": {"foreground": "#b9770e"},
    "muted": {"foreground": "#8a8a8a", "font": ("Consolas", 9)},
}

LIMIT_CHOICES = ["不限时", "1", "2", "5", "10", "30", "60", "300", "600", "1800", "3600"]


class App:
    def __init__(self, root):
        self.root = root
        self.q = queue_mod.Queue()
        self.runner = None
        self.running = False
        self.runner_pids = []
        self._closing = False
        self._slots = {}
        self._next_seq = 0
        self._outstanding = 0

        ncpu = os.cpu_count() or 4

        root.title("大数分解可视化 · 每个数量级分解前三个数（多进程并行版）")
        root.geometry("1180x820")

        # 底部两栏先按 side=bottom 锚定，保证任何窗口高度下都可见
        bottom = ttk.Frame(root, padding=(10, 0, 10, 8))
        bottom.pack(side="bottom", fill="x")
        self.pbar = ttk.Progressbar(bottom, mode="indeterminate", length=140)
        self.pbar.pack(side="left")
        self.var_status = tk.StringVar(value="就绪 —— 输入 N 后点击「开始分解」")
        ttk.Label(bottom, textvariable=self.var_status, padding=(10, 2)).pack(side="left")

        sysbar = ttk.Frame(root, padding=(10, 2))
        sysbar.pack(side="bottom", fill="x")
        self.var_sys = tk.StringVar(value="读取电脑信息…")
        ttk.Label(sysbar, textvariable=self.var_sys, foreground="#555",
                  wraplength=1050, justify="left").pack(fill="x")

        top = ttk.Frame(root, padding=(10, 10, 10, 2))
        top.pack(fill="x")
        ttk.Label(top, text="输入 N：").pack(side="left")
        self.var_n = tk.StringVar()
        ent = ttk.Entry(top, textvariable=self.var_n, width=27, font=("Consolas", 11))
        ent.pack(side="left", padx=(2, 8))
        ent.focus_set()
        ent.bind("<Return>", lambda _e: self.start())
        ttk.Label(top, text="限时:").pack(side="left")
        self.var_limit = tk.StringVar(value="10")
        ttk.Combobox(top, textvariable=self.var_limit, values=LIMIT_CHOICES,
                     width=6).pack(side="left", padx=(2, 8))
        ttk.Label(top, text="进程数:").pack(side="left")
        self.var_workers = tk.IntVar(value=ncpu)
        ttk.Spinbox(top, from_=1, to=max(ncpu, 1), increment=1,
                    textvariable=self.var_workers, width=4).pack(side="left", padx=(2, 8))
        self.btn_start = ttk.Button(top, text="开始分解", command=self.start)
        self.btn_start.pack(side="left")
        self.btn_pause = ttk.Button(top, text="暂停", command=self.toggle_pause,
                                    state="disabled")
        self.btn_pause.pack(side="left", padx=(4, 0))
        self.btn_skip = ttk.Button(top, text="跳过当前", command=self.skip_current,
                                   state="disabled")
        self.btn_skip.pack(side="left", padx=(4, 0))
        self.btn_stop = ttk.Button(top, text="停止", command=self.stop, state="disabled")
        self.btn_stop.pack(side="left", padx=(4, 0))

        mid = ttk.Frame(root, padding=(10, 2))
        mid.pack(fill="x")
        ttk.Label(mid, text="分解模式：").pack(side="left")
        self.var_mode = tk.StringVar(value="full")
        ttk.Radiobutton(mid, text="完整质因数分解", value="full",
                        variable=self.var_mode).pack(side="left")
        ttk.Radiobutton(mid, text="仅分解为两个数相乘（找到一个因子、证明是合数即可）",
                        value="two", variable=self.var_mode).pack(side="left", padx=(10, 0))

        hint = ("说明：对每个数量级 10^k（k = 0,1,2,…），取该数量级的前三个数 10^k、10^k+1、10^k+2"
                "（最后一组不超过 N）按所选模式分解。质数红色标出；限时未完成/跳过的橙色标出；"
                "大数以 10^n、10^n+d 或 a.bc×10^n 缩写显示。慢任务会打印中间过程。")
        ttk.Label(root, text=hint, wraplength=1050, justify="left", foreground="#555",
                  padding=(12, 2)).pack(fill="x")

        self.txt = scrolledtext.ScrolledText(root, font=("Consolas", 10), wrap="char",
                                             state="disabled", bg="#fcfcf8")
        self.txt.pack(fill="both", expand=True, padx=10, pady=6)
        for tag, kw in TAGS.items():
            self.txt.tag_configure(tag, **kw)

        root.protocol("WM_DELETE_WINDOW", self._on_close)
        root.after(80, self._poll)
        threading.Thread(target=self._monitor_loop, daemon=True).start()

    # ---------------- 运行控制 ----------------

    def _parse_limit(self):
        s = str(self.var_limit.get()).strip()
        if s in ("不限时", ""):
            return None
        try:
            return min(max(int(float(s)), 1), 86400)
        except Exception:
            raise ValueError("「每数限时」请选/填正整数秒，或选「不限时」")

    def start(self):
        if self.running:
            return
        try:
            N = parse_input(self.var_n.get())
        except ValueError as ex:
            messagebox.showerror("输入有误", str(ex))
            return
        except Exception:
            messagebox.showerror("输入有误", "数值格式不正确或过大")
            return
        try:
            limit = self._parse_limit()
        except ValueError as ex:
            messagebox.showerror("输入有误", str(ex))
            return
        try:
            workers = int(self.var_workers.get())
        except Exception:
            workers = os.cpu_count() or 1
        workers = max(1, min(workers, (os.cpu_count() or 1) * 2))
        mode = self.var_mode.get()
        groups = len(str(N))
        if groups > 400 and not messagebox.askyesno(
                "确认",
                f"N 有 {groups} 位，将处理 {groups} 个数量级（共 {count_numbers(N)} 个数），\n"
                f"可能耗时非常久。确定继续吗？"):
            return
        self.running = True
        self._slots = {}
        self._next_seq = 0
        self._outstanding = 0
        self.txt.configure(state="normal")
        self.txt.delete("1.0", "end")
        self.txt.configure(state="disabled")
        mode_txt = "完整质因数分解" if mode == "full" else "仅分解为两数相乘（证合数）"
        self._append(
            f"输入 N = {pretty_num(N, 80)}（{len(str(N))} 位）｜模式：{mode_txt}"
            f"｜{workers} 进程｜每数限时 {'不限时' if limit is None else str(limit) + ' 秒'}\n"
            "规则：每个数量级 10^k 取前三个数 10^k、10^k+1、10^k+2；\n"
            "      红色 = 质数；橙色 = 限时未完成/已跳过；缩写：10^n、10^n+d、a.bc×10^n。\n"
            + "─" * 78 + "\n", None)
        self.btn_start["state"] = "disabled"
        for b in (self.btn_pause, self.btn_stop):
            b["state"] = "normal"
        self.btn_pause["text"] = "暂停"
        self.btn_skip["state"] = "disabled"
        self.pbar.start(50)
        self.var_status.set(f"正在启动 {workers} 个计算进程…")
        self.runner = PoolRunner(N, limit, mode, workers, self.q)
        self.runner_pids = self.runner.pids
        self.runner.start()
        self.runner_pids = self.runner.pids

    def toggle_pause(self):
        if not self.running or self.runner is None:
            return
        if self.btn_pause["text"] == "暂停":
            self.runner.pause()
            self.btn_pause["text"] = "继续"
        else:
            self.runner.resume()
            self.btn_pause["text"] = "暂停"

    def skip_current(self):
        if self.running and self.runner is not None:
            self.runner.skip_current()

    def stop(self):
        if self.running and self.runner is not None:
            self.runner.stop()
            self.btn_stop["state"] = "disabled"
            self.btn_pause["state"] = "disabled"
            self.var_status.set("正在停止…")

    def _finish(self, status_text):
        self.running = False
        self.btn_start["state"] = "normal"
        self.btn_pause["state"] = "disabled"
        self.btn_pause["text"] = "暂停"
        self.btn_skip["state"] = "disabled"
        self.btn_stop["state"] = "disabled"
        self.pbar.stop()
        self.var_status.set(status_text)

    def _on_close(self):
        self._closing = True
        try:
            if self.runner is not None:
                self.runner.close()
        finally:
            self.root.destroy()

    # ---------------- 界面刷新 ----------------

    def _append(self, text, tag=None):
        self.txt.configure(state="normal")
        if tag:
            self.txt.insert("end", text, tag)
        else:
            self.txt.insert("end", text)
        self.txt.see("end")
        self.txt.configure(state="disabled")

    def _feed_slot(self, seq, text, tag):
        self._slots[seq] = (text, tag)
        while self._next_seq in self._slots:
            t, g = self._slots.pop(self._next_seq)
            self._append(t, g)
            self._next_seq += 1

    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "slot":
                    self._feed_slot(msg[1], msg[2], msg[3])
                elif kind == "progline":
                    self._append(msg[1] + "\n", "muted")
                elif kind == "status":
                    self.var_status.set(msg[1])
                elif kind == "outstanding":
                    self._outstanding = msg[1]
                    if self.running:
                        self.btn_skip["state"] = "normal" if msg[1] > 0 else "disabled"
                elif kind == "sysinfo":
                    self.var_sys.set(msg[1])
                elif kind == "summary":
                    self._append(msg[1], None)
                    self._finish(msg[2])
                elif kind == "error":
                    self._append("\n" + msg[1] + "\n", "hard")
                    self._finish("出错，详见结果区")
                    messagebox.showerror("错误", msg[1])
        except queue_mod.Empty:
            pass
        if not self._closing:
            self.root.after(80, self._poll)

    def _monitor_loop(self):
        prev_sys = _system_times()
        prev_pid = {}
        ncpu = os.cpu_count() or 1
        while not self._closing:
            time.sleep(2.0)
            if self._closing:
                break
            try:
                pids = [os.getpid()]
                if self.runner is not None:
                    pids += self.runner.alive_pids()
                cur_pid = {}
                cpu_dt = 0.0
                mem = 0
                alive = 0
                for pid in pids:
                    t = _proc_cpu_time(pid)
                    if t is None:
                        continue
                    alive += 1
                    cur_pid[pid] = t
                    cpu_dt += max(0.0, t - prev_pid.get(pid, t))
                    w = _proc_workingset(pid)
                    if w:
                        mem += w
                prev_pid = cur_pid
                cur_sys = _system_times()
                sys_txt = ""
                if prev_sys and cur_sys:
                    d_idle = cur_sys[0] - prev_sys[0]
                    d_total = (cur_sys[1] + cur_sys[2]) - (prev_sys[1] + prev_sys[2])
                    if d_total > 0:
                        sys_txt = f"整机 CPU {max(0.0, 1 - d_idle / d_total) * 100:.0f}%"
                prev_sys = cur_sys
                cores = cpu_dt / 2.0
                ram = _ram_info()
                if ram:
                    load, total, avail = ram
                    ram_txt = f"内存 {_fmt_bytes(total)}（可用 {_fmt_bytes(avail)}，已用 {load}%）"
                else:
                    ram_txt = "内存信息不可用"
                text = (f"电脑：{get_cpu_name()}｜{ncpu} 线程｜{sys_txt}｜{ram_txt}\n"
                        f"本程序：{alive} 个进程 · CPU ≈{cores:.1f} 核"
                        f"（{cores / ncpu * 100:.0f}%）· 占用内存 {_fmt_bytes(mem)}")
                self.q.put(("sysinfo", text))
            except Exception:
                continue


# ------------------------------------------------------------------ 自检与入口

def _next_prime(x):
    while not is_prime(x):
        x += 1
    return x


def selftest():
    ev = threading.Event()
    assert build_tasks(1) == [[1]]
    assert build_tasks(10) == [[1, 2, 3], [10]]
    assert build_tasks(12) == [[1, 2, 3], [10, 11, 12]]
    assert build_tasks(10001) == [[1, 2, 3], [10, 11, 12], [100, 101, 102],
                                  [1000, 1001, 1002], [10000, 10001]]
    # 缩写显示
    assert pretty_num(10 ** 21) == "10^21"
    assert pretty_num(10 ** 21 + 1) == "10^21+1"
    assert pretty_num(10 ** 21 + 2) == "10^21+2"
    assert pretty_num(10 ** 9) == "10^9"
    assert pretty_num(10 ** 9 + 1) == "10^9+1"
    assert pretty_num(10 ** 9 + 2) == "10^9+2"
    assert pretty_num(12345) == "12345"
    assert pretty_num(123456789) == "123456789"
    assert pretty_num(999999999999999989) == "999999999999999989"
    assert "×10^" in pretty_num(3 ** 60)
    assert pretty_num(10 ** 40 + 5) == "10^40+5"
    # 素性
    assert is_prime(1) is False
    assert is_prime(2) is True
    assert is_prime(999999999999999989) is True     # 10^18 以下最大素数
    assert is_prime(999999999999999990) is False
    assert is_prime(2 ** 61 - 1) is True            # 梅森素数
    # 完整分解
    dl = time.perf_counter() + 60
    ctl = Ctl(stop_event=ev, deadline=dl)
    f, hard = factorize(123456789, ctl)
    assert f == {3: 2, 3607: 1, 3803: 1} and not hard, (f, hard)
    f, hard = factorize(10 ** 18 + 1, ctl)
    assert not hard
    prod = 1
    for p, e in f.items():
        prod *= p ** e
    assert prod == 10 ** 18 + 1
    print("10^18+1 =", fmt_factors(f))
    # 两数相乘模式
    d, cof = factorize_two(91, ctl)
    assert d * cof == 91 and {d, cof} == {7, 13}
    assert factorize_two(2 ** 61 - 1, ctl) is None
    d, cof = factorize_two(10 ** 21 + 1, ctl)
    assert d * cof == 10 ** 21 + 1
    print(f"10^21+1 = {d} × {cof}（证合数模式）")
    # 限时路径：60 位半素数 1 秒内应超时
    random.seed(7)
    semi = (_next_prime(random.randrange(10 ** 29, 10 ** 30) | 1)
            * _next_prime(random.randrange(10 ** 29, 10 ** 30) | 1))
    try:
        factorize(semi, Ctl(stop_event=ev, deadline=time.perf_counter() + 1.0))
        raise AssertionError("60 位半素数应在限时内超时")
    except FactorTimeout as e:
        facs, rem = e.args
        assert not facs and rem == [semi], (facs, rem)
    print("限时超时路径 OK")
    # 跳过路径
    sk = threading.Event()
    sk.set()
    try:
        factorize(semi, Ctl(stop_event=threading.Event(), skip_event=sk,
                            deadline=None))
        raise AssertionError("应触发跳过")
    except SkipRequested:
        pass
    print("跳过路径 OK")
    selftest_pool()
    selftest_skip_in_pool(semi)
    print("SELFTEST OK")


def selftest_pool():
    """多进程流水线：顺序、完整性。"""
    N = 10 ** 6
    out_q = queue_mod.Queue()
    runner = PoolRunner(N, limit=10, mode="full", workers=4, out_q=out_q)
    runner.start()
    slots = {}
    nxt = 0
    summary = None
    deadline = time.time() + 120
    while summary is None and time.time() < deadline:
        try:
            msg = out_q.get(timeout=1.0)
        except queue_mod.Empty:
            continue
        if msg[0] == "slot":
            slots[msg[1]] = (msg[2], msg[3])
            while nxt in slots:
                slots.pop(nxt)
                nxt += 1
        elif msg[0] == "summary":
            summary = msg
    runner.close()
    assert summary is not None, "流水线未在限时内完成"
    assert nxt == 7 + count_numbers(N), (nxt, 7 + count_numbers(N))  # 7 个数量级标题 + 19 个数
    print("多进程流水线（顺序+完整性）OK")


def selftest_skip_in_pool(semi):
    """多进程中的跳过/停止：事件能打断不限时任务。"""
    ctx = multiprocessing.get_context("spawn")
    task_q = ctx.Queue()
    result_q = ctx.Queue()
    stop_ev = ctx.Event()
    skip_ev = ctx.Event()
    p = ctx.Process(target=_pool_worker, args=(task_q, result_q, stop_ev, skip_ev))
    p.start()
    task_q.put((0, semi, None, "full"))
    time.sleep(1.5)
    skip_ev.set()
    msg = result_q.get(timeout=60)
    assert msg[0] == "result" and msg[2] == "skipped", msg
    skip_ev.clear()
    stop_ev.clear()
    task_q.put((1, semi, None, "two"))
    time.sleep(1.5)
    stop_ev.set()
    msg = result_q.get(timeout=60)
    assert msg[0] == "result" and msg[2] == "stopped", msg
    task_q.put(None)
    p.join(timeout=10)
    if p.is_alive():
        p.terminate()
    print("多进程跳过/停止 OK")


def main():
    multiprocessing.freeze_support()   # PyInstaller 打包后子进程必需
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    if "--selftest" in sys.argv:
        selftest()
        return
    root = tk.Tk()
    app = App(root)
    if "--demo" in sys.argv:
        app.var_n.set("10^12")
        root.after(800, app.start)   # 演示模式：自动开始分解 10^12
    root.mainloop()


if __name__ == "__main__":
    main()
