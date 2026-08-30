# -*- coding: utf-8 -*-
"""
大数分解可视化工具（多进程并行版，纯 Python 标准库，界面为 tkinter）

功能
====
1. 输入一个很大的正整数 N（支持 10^100、2^64、1e50 写法或直接粘贴）。
2. 对每个数量级 10^k（k = 0,1,2,… 直到 N 的数量级）：从 10^k 起逐个向上扫描，
   **找出该数量级的前 3 个质数**（可能要测试很多个数）；途中经过的合数也按所选模式
   分解后列出（最后一组不超过 N）。
   两种分解模式（可单选）：
   · 完整质因数分解：分解成所有质因数之积；
   · 仅分解为两个数相乘：找到一个非平凡因子 d，给出 n = d × (n/d)，即可证明 n 是合数。
3. 大数一律缩写显示：10^n、10^n+d 或 a.bcd×10^n，不再是一长串 0。
4. 质数用红色标出；限时内未能完成 / 被跳过的内容用橙色标出。
5. 多进程并行：按 CPU 核数开计算进程（可调），每个数量级一个任务，结果按顺序显示；
   组内 = 号对齐、「用时」列对齐。
6. 限时（作用于每个数量级）可选「不限时」；运行中可 暂停/继续、跳过当前、停止。
7. 慢任务中间过程：持续打印当前进度（已扫描多少个数、找到几个质数、rho/p-1/MR 各阶段）。
8. 界面下方实时显示电脑基本信息（CPU 型号/线程数、整机 CPU 占用、内存）和
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
PRIMES_PER_GROUP = 3          # 每个数量级要找出的质数个数

try:
    sys.set_int_max_str_digits(2_000_000)   # Python 3.11+ 默认 int/str 限制 4300 位
except AttributeError:
    pass


class FactorTimeout(Exception):
    """限时内未能完成。args 含部分结果"""


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


def _primes_total():
    return len(get_primes())


class Ctl:
    """协同取消（停止/跳过/暂停/限时）+ 慢任务进度上报。"""
    __slots__ = ("stop_event", "skip_event", "pause_event", "deadline", "prog",
                 "seq", "widx", "t0", "last_note", "last_trial")

    def __init__(self, stop_event=None, skip_event=None, pause_event=None,
                 deadline=None, prog=None, seq=0, widx=0):
        self.stop_event = stop_event
        self.skip_event = skip_event
        self.pause_event = pause_event
        self.deadline = deadline
        self.prog = prog            # mp.Queue；None 表示不上报进度（如自检）
        self.seq = seq
        self.widx = widx
        self.t0 = time.perf_counter()
        self.last_note = 0.0
        self.last_trial = 0.0

    def elapsed(self):
        return time.perf_counter() - self.t0

    def check(self):
        if self.skip_event is not None and self.skip_event.is_set():
            raise SkipRequested()
        if self.stop_event is not None and self.stop_event.is_set():
            raise StopRequested()
        if self.pause_event is not None and self.pause_event.is_set():
            # 真·暂停：就地冻结，期间仍响应停止/跳过
            while self.pause_event.is_set():
                if self.stop_event is not None and self.stop_event.is_set():
                    raise StopRequested()
                if self.skip_event is not None and self.skip_event.is_set():
                    raise SkipRequested()
                time.sleep(0.1)
        if self.deadline is not None and time.perf_counter() >= self.deadline:
            raise FactorTimeout()

    def note(self, text):
        """中间过程：任务运行 2 秒后才开始上报，且最多每秒一条。"""
        if self.prog is None:
            return
        now = time.perf_counter()
        if now - self.t0 < 2.0 or now - self.last_note < 1.0:
            return
        self.last_note = now
        try:
            self.prog.put(("prog", self.seq, self.widx, round(now - self.t0, 1), text))
        except Exception:
            pass

    def trial(self, idx, total, p):
        """试除进度：当前试到第几个素数（限速每秒最多 10 次）。"""
        if self.prog is None:
            return
        now = time.perf_counter()
        if now - self.last_trial < 0.1:
            return
        self.last_trial = now
        try:
            self.prog.put(("trial", self.seq, self.widx,
                           f"正在试除找小因子：第 {idx}/{total} 个素数（当前试到 {p}）"))
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
            ctl.note(f"正在验证是否为质数（第 {bi}/{len(bases)} 轮，预计还需 ~{eta:.0f} 秒）")
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
            ctl.note(f"正在用 p-1 方法找因子（进度 {i}/{total}）")
    g = math.gcd(a - 1, n)
    return g if 1 < g < n else None


def _fmt_wan(x):
    """按“万”为单位的友好计数。"""
    if x >= 1e8:
        return f"{x / 1e8:.2f} 亿"
    if x >= 1e4:
        return f"{x / 1e4:.0f} 万"
    return f"{x:.0f}"


class _EcmFound(Exception):
    """ECM 过程中模逆失败：携带的 g = gcd(分子, n) 就是 n 的一个因子。"""

    def __init__(self, g):
        super().__init__(g)
        self.g = g


def _inv(x, n):
    """扩展欧几里得求逆元；不互素时抛 _EcmFound(gcd)。"""
    old_r, r = x % n, n
    old_s, s = 1, 0
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
    if old_r == 1:
        return old_s % n
    raise _EcmFound(old_r)


def _pt_add(P, Q, a, n):
    """椭圆曲线点加（仿射坐标），曲线 y² = x³ + a·x + b (mod n)。None 为无穷远点。"""
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2:
        if (y1 + y2) % n == 0:
            return None
        lam = (3 * x1 * x1 + a) * _inv(2 * y1, n) % n
    else:
        lam = (y2 - y1) * _inv((x2 - x1) % n, n) % n
    x3 = (lam * lam - x1 - x2) % n
    return (x3, (lam * (x1 - x3) - y1) % n)


def _pt_mul(k, P, a, n):
    """椭圆曲线标量乘（双倍-加法）。"""
    R = None
    add = P
    while k:
        if k & 1:
            R = _pt_add(R, add, a, n)
        k >>= 1
        if k:
            add = _pt_add(add, add, a, n)
    return R


ECM_MAX_BITS = 10_000        # 超过该位数不做 ECM
ECM_B1 = 2_000               # ECM 第一阶段界限（纯 Python 演示级，详见算法调研报告）
ECM_MAX_CURVES = 30          # 最多尝试曲线数


def pollard_ecm(n, ctl, b1=ECM_B1, max_curves=ECM_MAX_CURVES):
    """Lenstra 椭圆曲线分解（ECM，第一阶段，简化仿射实现）。

    找到非平凡因子返回之；曲线用尽返回 None；限时/停止/跳过照常抛异常。
    """
    if n % 2 == 0:
        return 2
    primes = [p for p in get_primes() if p <= b1]
    for c in range(max_curves):
        ctl.check()
        a = random.randrange(6, n)
        x0 = random.randrange(1, n)
        y0 = random.randrange(1, n)
        b = (y0 * y0 - x0 * x0 * x0 - a * x0) % n
        P = (x0, y0)
        try:
            for p in primes:
                ctl.check()
                ctl.note(f"ECM 椭圆曲线：第 {c + 1}/{max_curves} 条曲线，"
                         f"B1={b1}，当前素数幂 {p}")
                k = p
                while k * p <= b1:
                    k *= p
                P = _pt_mul(k, P, a, n)
                if P is None:
                    break
        except _EcmFound as e:
            if 1 < e.g < n:
                return e.g
            continue          # g == n：曲线退化，换一条
    return None


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
                    ctl.note(f"正在用随机算法找因子（已试 {_fmt_wan(steps)} 步 · "
                             f"约 {_fmt_wan(rate)} 步/秒）——这类因子可能要找很久")
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


def factorize(n, ctl, alg="auto"):
    """完整质因数分解。正常返回 (因子 dict{素数: 次数}, 未分解剩余 list)。

    未分解剩余的元素为 (数, 原因)："toobig"=位数超限，"algfail"=所选算法未能分解。
    限时/停止/跳过时抛对应异常，args = (已分解因子 dict, 剩余未分解 list)。
    alg：auto（p-1→rho）/ rho / pm1 / ecm / deep（p-1→ECM→rho）。
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
            for pi, p in enumerate(get_primes(), 1):
                if p * p > m:
                    break
                if pi % 4096 == 0 and ctl is not None:
                    ctl.check()
                if ctl is not None:
                    ctl.trial(pi, _primes_total(), p)
                while m % p == 0:
                    factors[p] = factors.get(p, 0) + 1
                    m //= p
            cur = m
            if m == 1:
                cur = None
                continue
            if ctl is not None:
                ctl.check()
                ctl.note(f"小因子试除完成，剩余 {len(str(m))} 位，开始验证是否质数 / 找因子")
            pr = is_prime(m, ctl)
            if pr is True:
                factors[m] = factors.get(m, 0) + 1
                cur = None
                continue
            if pr is None or (alg in ("auto", "rho", "deep")
                              and m.bit_length() > RHO_MAX_BITS):
                hard.append((m, "toobig"))
                cur = None
                continue
            d = None
            if alg == "rho":
                d = pollard_brent(m, ctl)
            elif alg == "pm1":
                d = pollard_pm1(m, ctl) if m.bit_length() <= PM1_MAX_BITS else None
                if d is None:
                    hard.append((m, "algfail"))
                    cur = None
                    continue
            elif alg == "ecm":
                d = pollard_ecm(m, ctl) if m.bit_length() <= ECM_MAX_BITS else None
                if d is None:
                    hard.append((m, "algfail"))
                    cur = None
                    continue
            elif alg == "deep":
                if m.bit_length() <= PM1_MAX_BITS:
                    d = pollard_pm1(m, ctl)
                if d is None and m.bit_length() <= ECM_MAX_BITS:
                    d = pollard_ecm(m, ctl)
                if d is None:
                    d = pollard_brent(m, ctl)
            else:  # auto
                if m.bit_length() <= PM1_MAX_BITS:
                    d = pollard_pm1(m, ctl)
                if d is None:
                    d = pollard_brent(m, ctl)
            work.append(d)
            work.append(m // d)
            cur = None
    except (FactorTimeout, StopRequested, SkipRequested) as e:
        rest = [(w, "cut") for w in work if w > 1] + hard
        if cur is not None and cur > 1:
            rest.append((cur, "cut"))
        e.args = (dict(factors), rest)
        raise
    return factors, hard


def factorize_two(n, ctl, alg="auto"):
    """仅找一个非平凡因子：返回 (d, n//d) 证明合数；n 是质数返回 None。

    无法完成时抛 FactorTimeout（args=(已找到的 d 或 None,)）。
    """
    if n % 2 == 0:
        return (2, n // 2)
    for pi, p in enumerate(get_primes(), 1):
        if p * p > n:
            break
        if pi % 4096 == 0 and ctl is not None:
            ctl.check()
        if ctl is not None:
            ctl.trial(pi, _primes_total(), p)
        if n % p == 0:
            return (p, n // p)
    pr = is_prime(n, ctl)
    if pr is True:
        return None
    if ctl is not None:
        ctl.check()
        ctl.note("小因子试除完成，转入找因子算法")
    try:
        if alg in ("auto", "pm1", "deep") and n.bit_length() <= PM1_MAX_BITS:
            d = pollard_pm1(n, ctl)
            if d:
                return (d, n // d)
        if alg in ("ecm", "deep") and n.bit_length() <= ECM_MAX_BITS:
            d = pollard_ecm(n, ctl)
            if d:
                return (d, n // d)
        if alg in ("auto", "rho", "deep"):
            if n.bit_length() > RHO_MAX_BITS:
                raise FactorTimeout((None,))
            d = pollard_brent(n, ctl)
            return (d, n // d)
        raise FactorTimeout((None,))    # 所选算法不支持该位数
    except FactorTimeout as e:
        if not e.args:
            e.args = (None,)
        raise


# ------------------------------------------------------------------ 数量级扫描（找前 3 个质数）

def classify_number(n, mode, ctl, alg="auto"):
    """判定/分解单个数。返回 (kind, a, b)：
    unit / prime / full(合数,因子dict,None) / two(d,余因子) /
    timeout(部分因子,剩余) / twofail(d或None,None) / fullhard / stopped / skipped
    fullhard 的 b 为 (数, 原因) 列表，原因："toobig" / "algfail"
    """
    if n == 1:
        return ("unit", None, None)
    try:
        if mode == "two":
            r = factorize_two(n, ctl, alg)
            if r is None:
                return ("prime", None, None)
            return ("two", r[0], r[1])
        factors, hard = factorize(n, ctl, alg)
        if hard:
            return ("fullhard", factors, hard)
        if len(factors) == 1 and factors.get(n) == 1:
            return ("prime", None, None)
        return ("full", factors, None)
    except FactorTimeout as e:
        if mode == "two":
            return ("twofail", e.args[0] if e.args else None, None)
        f, r = e.args if len(e.args) == 2 else ({}, [(n, "cut")])
        return ("timeout", f, r)
    except StopRequested as e:
        if mode == "two":
            return ("stopped", None, None)
        f, r = e.args if len(e.args) == 2 else ({}, [(n, "cut")])
        return ("stopped", f, r)
    except SkipRequested:
        return ("skipped", None, None)


def scan_magnitude(k, N, mode, ctl, detail=False, ppn=PRIMES_PER_GROUP, alg="auto"):
    """一个数量级的扫描任务：从 10^k 起逐个向上，直到找出前 ppn 个质数。

    返回 (rows, primes_found, scanned, stop_kind)
    rows: [(num, kind, a, b, dt)]；stop_kind: None / timeout / stopped / skipped
    限时（若有）作用于整个数量级。detail=False 时不发送“找到质数”事件
    （紧凑显示下每组结果自带质数行，避免结果区刷屏）。
    """
    rows = []
    primes_found = 0
    scanned = 0
    stop_kind = None
    n = 10 ** k
    if ctl is not None:
        ctl.note(f"数量级 10^{k}：开始逐个检查，目标前 {ppn} 个质数")
    try:
        while primes_found < ppn and n <= N:
            if ctl is not None:
                ctl.check()
            if ctl is not None and ctl.prog is not None:
                try:
                    ctl.prog.put(("curnum", ctl.seq, ctl.widx, pretty_num(n, 40)))
                except Exception:
                    pass
            t1 = time.perf_counter()
            kind, a, b = classify_number(n, mode, ctl, alg)
            dt = time.perf_counter() - t1
            scanned += 1
            if kind == "prime":
                primes_found += 1
                if ctl is not None and ctl.prog is not None:
                    try:
                        ctl.prog.put(("milestone", ctl.seq, ctl.widx,
                                      f"找到本组第 {primes_found} 个质数：{pretty_num(n)}"
                                      f"（已检查 {scanned} 个数）"))
                    except Exception:
                        pass
            rows.append((n, kind, a, b, dt))
            n += 1
            if ctl is not None:
                ctl.note(f"已检查 {scanned} 个数，找到 {primes_found}/{ppn} 个质数")
    except FactorTimeout:
        stop_kind = "timeout"
    except StopRequested:
        stop_kind = "stopped"
    except SkipRequested:
        stop_kind = "skipped"
    return rows, primes_found, scanned, stop_kind


# ------------------------------------------------------------------ 显示辅助

def pretty_num(x, limit=18):
    """大数缩写：10^n / 10^n+d / a.bcd×10^n；短数直接显示。

    ≥10 位的数若为 10 的幂或 10^n 加小偏移，一律缩写（无论多长）；
    其余 ≤18 位照原样显示，更长的用 7 位有效数字的科学计数法（尾零去除）。
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
            mant = (s[0] + "." + s[1:7]).rstrip("0").rstrip(".")
            return f"{mant}×10^{k}"
    return s


def disp_width(s):
    """终端显示宽度：中文等全角字符按 2 计。"""
    return sum(2 if ord(ch) > 0x2E7F else 1 for ch in s)


def pad_to(s, width):
    return s + " " * max(0, width - disp_width(s))


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


HARD_KINDS = ("timeout", "stopped", "skipped", "fullhard", "twofail")


def fact_text(kind, a, b):
    """单个数的分解式文本（不含用时）。"""
    if kind == "unit":
        return "1（单位：既不是质数也不是合数）"
    if kind == "prime":
        return "质数"
    if kind == "two":
        return f"{pretty_num(a)} × {pretty_num(b)}"
    if kind == "twofail":
        return "？【限时内没找到任何因子——无法确定它是质数还是合数】"
    if kind in HARD_KINDS:
        note = {"timeout": "【限时内未能完全分解——剩余部分可能是质数，也可能是两个大质数的乘积】",
                "stopped": "【已停止，未算完】",
                "skipped": "【已跳过，未算完】",
                "fullhard": "【未能完全分解——剩余部分可能是质数，也可能是两个大质数的乘积】",
                "twofail": "【限时内没找到任何因子——无法确定它是质数还是合数】"}[kind]
        base = fmt_factors(a) if a else ""
        if b:
            parts = []
            for item in b:
                if isinstance(item, tuple):
                    r, why = item
                    suffix = {"algfail": "【所选算法未能分解，可换其它算法】",
                              "cut": "【随任务中断】"}.get(why, "")
                    parts.append(f"剩余 {len(str(r))} 位大数（{pretty_num(r, 36)}）{suffix}")
                else:
                    parts.append(f"剩余 {len(str(item))} 位大数（{pretty_num(item, 36)}）")
            rp = " × ".join(parts)
            body = f"{base} × {rp}{note}" if base else rp + note
        else:
            body = (base + note) if base else note
        return body
    return fmt_factors(a)


def group_header(k, N):
    lo = 10 ** k
    upper = f"10^{k + 1}-1" if k >= 1 else "9"
    if N < lo * 10:                       # 最后一个不完整的数量级
        upper = pretty_num(N, 30)
    return ("\n" + "─" * 12 + f" 数量级 10^{k}（{pretty_num(lo, 30)} ~ {upper}）"
            + "─" * 12 + "\n")


def render_group_lines(k, N, rows, primes_found, scanned, stop_kind,
                       detail=False, ppn=PRIMES_PER_GROUP):
    """把一个数量级的扫描结果渲染为对齐的行。

    返回 (header, [(line, tag)...], tail)。
    detail=False（紧凑，默认）：只列出质数、单位数和异常行（限时/跳过等），
    普通合数折叠为一行摘要；detail=True 逐个数列出。
    组内所有 = 号对齐、「用时」列对齐（中文按 2 倍宽度计算）。
    """
    header = group_header(k, N)
    if detail:
        shown = list(rows)
        n_comp = 0
    else:
        shown = [r for r in rows if r[1] == "unit" or r[1] == "prime"
                 or r[1] in HARD_KINDS]
        n_comp = sum(1 for r in rows if r[1] in ("full", "two"))
    maxnum = max((disp_width(pretty_num(num, 60)) for num, *_ in shown), default=0)
    facts = [fact_text(kind, a, b) for _num, kind, a, b, _dt in shown]
    maxf = max((disp_width(f) for f in facts), default=0)
    lines = []
    for (num, kind, a, b, dt), fs in zip(shown, facts):
        nd = pad_to(pretty_num(num, 60), maxnum)
        fsp = pad_to(fs, maxf)
        tag = "prime" if kind == "prime" else ("hard" if kind in HARD_KINDS else None)
        lines.append((f"  {nd} = {fsp}    用时 {fmt_time(dt)}\n", tag))
    if n_comp:
        lines.append((f"  —— 另扫描合数 {n_comp} 个，均已按所选模式分解完毕"
                      f"（勾选「列出合数明细」可逐个查看）\n", "muted"))
    if rows:
        slowest = sorted(rows, key=lambda r: r[4], reverse=True)[:3]
        ent = "、".join(f"{pretty_num(num, 40)}（用时 {fmt_time(dt)}）"
                        for num, _k, _a, _b, dt in slowest)
        lines.append((f"  —— 本组耗时最长的 {len(slowest)} 个数：{ent}\n", "muted"))
    if stop_kind is not None:
        note = {"timeout": f"【本组限时已到：检查了 {scanned} 个数，只找到 {primes_found}/{ppn} 个质数——可调大「每组限时」或选「不限时」重跑】",
                "stopped": f"【已停止：检查了 {scanned} 个数，找到 {primes_found}/{ppn} 个质数】",
                "skipped": f"【已跳过本组：检查了 {scanned} 个数，找到 {primes_found}/{ppn} 个质数】"}[stop_kind]
        tail = (f"  {note}\n", "hard")
    elif primes_found >= ppn:
        tail = (f"  —— 本组共检查 {scanned} 个数，找到前 {ppn} 个质数\n", "muted")
    else:
        tail = (f"  —— 已到 N，本组共检查 {scanned} 个数，质数 {primes_found} 个\n", "muted")
    return header, lines, tail


# ------------------------------------------------------------------ 输入

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

def _do_group_task(seq, k, N, limit, mode, detail, ppn, alg,
                   stop_event, skip_event, pause_event, widx, result_q):
    """在计算进程里处理一个数量级：扫描并渲染好整组行。"""
    deadline = None if not limit else time.perf_counter() + limit
    ctl = Ctl(stop_event, skip_event, pause_event, deadline,
              prog=result_q, seq=seq, widx=widx)
    t1 = time.perf_counter()
    try:
        rows, pf, scanned, stop_kind = scan_magnitude(k, N, mode, ctl, detail, ppn, alg)
        header, lines, tail = render_group_lines(k, N, rows, pf, scanned,
                                                 stop_kind, detail, ppn)
        payload = (header, lines, tail, pf, scanned)
        return ("result", seq, widx, "group", payload, None, time.perf_counter() - t1)
    except Exception as e:
        return ("result", seq, widx, "gerror", f"{type(e).__name__}: {e}", None,
                time.perf_counter() - t1)


def _pool_worker(task_q, result_q, stop_event, skip_event, pause_event, widx):
    """计算进程主循环：取任务 → 计算 → 回传；收到 None 哨兵退出。"""
    while True:
        try:
            task = task_q.get()
        except (EOFError, OSError):
            return
        if task is None:
            return
        seq, k, N, limit, mode, detail, ppn, alg = task
        skip_event.clear()    # 新任务开始：清除上一组遗留的跳过标记（按组跳过不级联）
        try:
            res = _do_group_task(seq, k, N, limit, mode, detail, ppn, alg,
                                 stop_event, skip_event, pause_event, widx, result_q)
        except Exception as e:
            res = ("result", seq, widx, "gerror", repr(e), None, 0.0)
        try:
            result_q.put(res)
        except Exception:
            return


class PoolRunner:
    """多进程流水线：每个数量级一个任务，结果按数量级顺序回传给界面。

    out_q 消息：
      ("slot", seq, content)     content = [(text, tag), ...] 按顺序显示的一组行
      ("progline", text)         慢任务中间过程
      ("status", text) / ("outstanding", n)
      ("summary", text, status_text) / ("error", text)
    """

    def __init__(self, N, limit, mode, workers, out_q, detail=False,
                 ppn=PRIMES_PER_GROUP, alg="auto"):
        self.N = N
        self.limit = limit            # None = 不限时
        self.mode = mode              # "full" / "two"
        self.detail = detail          # True = 列出全部合数明细
        self.ppn = max(1, int(ppn))   # 每组要找的质数个数
        self.alg = alg                # 找因子算法：auto/rho/pm1/ecm/deep
        self.workers = max(1, int(workers))
        self.out_q = out_q
        self.pids = []
        self.cpu_by_pid = {}          # pid -> 该进程 CPU 占用%（监控线程写入）
        self._procs = []
        self._task_q = None
        self._result_q = None
        self._stop_event = None
        self._skip_events = []        # 每个计算进程独立的跳过事件（支持按组跳过）
        self._pause_event = None
        self._stop_flag = False
        self._paused = False
        self._exhausted = False
        self._finished = False
        self._outstanding = {}        # seq -> (k, pretty, t_submit)
        self._prog_detail = {}        # seq -> (elapsed, 最新进度文本)
        self._curnum = {}             # seq -> (正在算的数, 该数开始时刻)
        self._widx = {}               # seq -> 计算进程编号
        self._pending_item = None
        self._seq = 0
        self._items = None
        self._stats = {"n": 0, "prime": 0, "partial": 0, "fact": 0.0, "scanned": 0}
        self._done = 0
        self._total = len(str(N))     # 每个数量级一组
        self._t0 = time.perf_counter()

    def busy_count(self):
        return len(self._outstanding)

    def skip_one(self, seq):
        """只跳过指定数量级（该组所在计算进程的独立事件）。"""
        widx = self._widx.get(seq)
        if widx is not None and 0 <= widx < len(self._skip_events):
            self._skip_events[widx].set()

    def skip_all(self):
        """跳过当前正在计算的所有组（各进程完成当前组后自动恢复接新任务）。"""
        for e in self._skip_events:
            e.set()

    def start(self):
        ctx = multiprocessing.get_context("spawn")
        self._task_q = ctx.Queue()
        self._result_q = ctx.Queue()
        self._stop_event = ctx.Event()
        self._pause_event = ctx.Event()
        self._skip_events = [ctx.Event() for _ in range(self.workers)]
        for widx in range(self.workers):
            p = ctx.Process(target=_pool_worker,
                            args=(self._task_q, self._result_q,
                                  self._stop_event, self._skip_events[widx],
                                  self._pause_event, widx),
                            daemon=True)
            p.start()
            self._procs.append(p)
            self.pids.append(p.pid)
        self._items = self._iter_groups()
        threading.Thread(target=self._feeder_loop, daemon=True).start()

    def _iter_groups(self):
        k = 0
        while 10 ** k <= self.N:
            yield ("group", k)
            k += 1

    def pause(self):
        self._paused = True
        if self._pause_event is not None:
            self._pause_event.set()      # 真·暂停：正在算的组就地冻结

    def resume(self):
        self._paused = False
        if self._pause_event is not None:
            self._pause_event.clear()

    def skip_current(self):
        """跳过当前正在计算的所有组（F10）。"""
        self.skip_all()

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

    def _refill(self):
        while not self._stop_flag and not self._paused \
                and len(self._outstanding) < self.workers and not self._exhausted:
            if self._pending_item is None:
                try:
                    self._pending_item = next(self._items)
                except StopIteration:
                    self._exhausted = True
                    return
            _, k = self._pending_item
            seq = self._seq
            self._task_q.put((seq, k, self.N, self.limit, self.mode,
                              self.detail, self.ppn, self.alg))
            self._outstanding[seq] = (k, f"数量级 10^{k}", time.perf_counter())
            self._seq += 1
            self._pending_item = None

    def _on_result(self, msg):
        _, seq, _widx, kind, a, b, dt = msg
        info = self._outstanding.pop(seq, None)
        self._prog_detail.pop(seq, None)
        self._curnum.pop(seq, None)
        self._widx.pop(seq, None)
        if info is None:
            return
        if kind == "group":
            header, lines, tail, pf, scanned = a
            content = [(header, "group")] + [tuple(x) for x in lines]
            if tail:
                content.append(tuple(tail))
            self.out_q.put(("slot", seq, content))
            self._done += 1
            self._stats["n"] += 1
            self._stats["prime"] += pf
            self._stats["fact"] += dt
            self._stats["scanned"] += scanned
            if tail and tail[1] == "hard":
                self._stats["partial"] += 1
        else:  # gerror
            self.out_q.put(("slot", seq, [(f"  数量级计算出错：{a}\n", "hard")]))
            self._done += 1
            self._stats["partial"] += 1

    @staticmethod
    def _phase_of(text):
        """从最新进度文本推断当前阶段（用于状态栏）。"""
        if not text:
            return "逐个检查中"
        if "试除找小因子" in text:
            return "试除找小因子"
        if "随机算法" in text or "rho" in text:
            return "寻找因子"
        if "p-1" in text:
            return "预处理找因子"
        if "验证" in text or "试除完成" in text:
            return "验证是否质数"
        return "逐个检查中"

    def _post_status(self):
        now = time.perf_counter()
        items = []
        for _seq, (k, _pretty, t) in sorted(self._outstanding.items())[:5]:
            detail = self._prog_detail.get(_seq)
            phase = self._phase_of(detail[1] if detail else None)
            items.append(f"数量级 10^{k}（已 {now - t:.0f} 秒，{phase}）")
        infl = "｜".join(items)
        txt = (f"已完成 {self._done}/{self._total} 个数量级 · 已检查 {self._stats['scanned']} 个数"
               + (f" · 正在算：{infl}" if infl else "")
               + (" · 已暂停" if self._paused else "")
               + (" · 正在停止…" if self._stop_flag else "")
)
        self.out_q.put(("status", txt))
        self.out_q.put(("outstanding", len(self._outstanding)))

    @staticmethod
    def _short_status(text):
        """把最新进度文本压缩成适合放进进度行的短语。"""
        if not text:
            return "逐个检查中"
        if text.startswith("已检查"):
            return "逐个检查中"
        if "——" in text:
            text = text.split("——")[0]
        return text.rstrip("：: ")

    def _post_progress_line(self, now):
        """进行中的组汇总：一个数量级一行，含正在算的数、其耗时与所用进程。"""
        if self._paused:
            rows = [(None, "[已暂停] 正在计算的组已就地冻结（点「继续」恢复）")]
        elif not self._outstanding:
            rows = [(None, "[正在计算] 等待计算结果…")]
        else:
            busy = len(self._outstanding)
            idle = max(0, self.workers - busy)
            rows = [(None, f"[正在计算] 共 {busy} 组 · 进程 {self.workers} 个"
                           f"（忙碌 {busy}，空闲 {idle}，每组占 1 个）")]
            for seq, (k, _pretty, t) in sorted(self._outstanding.items()):
                if len(rows) > 12:
                    rows.append((None, f"……其余 {len(self._outstanding) - 12} 组进行中"))
                    break
                detail = self._prog_detail.get(seq)
                status = self._short_status(detail[1] if detail else None)
                widx = self._widx.get(seq)
                wtxt = ""
                if widx is not None:
                    pid = self.pids[widx] if widx < len(self.pids) else None
                    pct = self.cpu_by_pid.get(pid)
                    wtxt = f" · 进程#{widx + 1}" + (f"（CPU {pct:.0f}%）" if pct else "")
                cur = self._curnum.get(seq)
                if cur:
                    rows.append((seq, f"数量级 10^{k}（本组已 {now - t:.0f} 秒）"
                                       f"正在算 {cur[0]}（该数已 {now - cur[1]:.0f} 秒，"
                                       f"{status}）{wtxt}"))
                else:
                    rows.append((seq, f"数量级 10^{k}（本组已 {now - t:.0f} 秒，"
                                      f"{status}）{wtxt}"))
        self.out_q.put(("progress_rows", rows))

    def _feeder_loop(self):
        try:
            last_status = 0.0
            last_prog_line = 0.0
            while True:
                while True:                      # 1) 收结果/进度
                    try:
                        msg = self._result_q.get(timeout=0.02)
                    except queue_mod.Empty:
                        break
                    except (OSError, ValueError):
                        break
                    if msg[0] == "prog":
                        _, seq, widx, elapsed, text = msg
                        self._widx[seq] = widx
                        self._prog_detail[seq] = (elapsed, text)
                    elif msg[0] == "trial":
                        _, seq, widx, text = msg
                        self._widx[seq] = widx
                        self._prog_detail[seq] = (None, text)
                    elif msg[0] == "curnum":
                        _, seq, widx, ntext = msg
                        self._widx[seq] = widx
                        self._curnum[seq] = (ntext, time.perf_counter())
                    elif msg[0] == "milestone":
                        _, seq, widx, text = msg
                        self._widx[seq] = widx
                        info = self._outstanding.get(seq)
                        if info:
                            self.out_q.put(("milestone",
                                            f"[{info[1]}] {text}"))
                    elif msg[0] == "result":
                        self._on_result(msg)
                self._refill()                   # 2) 填充任务
                now = time.perf_counter()        # 3) 状态与进度行
                if now - last_status >= 0.4:
                    last_status = now
                    self._post_status()
                if now - last_prog_line >= 1.0:
                    last_prog_line = now
                    self._post_progress_line(now)
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
        mode_txt = "完整质因数分解" if self.mode == "full" else "只分解成两数相乘（证明是合数即可）"
        limit_txt = "不限时" if not self.limit else f"每组限时 {self.limit} 秒"
        head = "已停止" if self._stop_flag else "全部完成"
        summary = (
            "\n" + "═" * 78 + "\n"
            + f"{head}｜模式：{mode_txt}｜{self.workers} 个进程同时计算｜{limit_txt}\n"
            + f"共检查 {s['n']}/{self._total} 个数量级、{s['scanned']} 个数："
            + f"找到质数 {s['prime']} 个；没找满 3 个质数的数量级有 {s['partial']} 个"
            + "（多为限时所致，可调大每组限时或选「不限时」重跑）\n"
            + f"分解计算总用时 {fmt_time(s['fact'])}（从开始到结束共 {fmt_time(wall)}）\n")
        status = (f"{head} · 已检查 {s['n']}/{self._total} 个数量级 · 质数 {s['prime']} 个"
                  + (f" · 没找满 3 个质数 {s['partial']} 组" if s["partial"] else "")
                  + f" · 分解计算总用时 {fmt_time(s['fact'])}")
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

LIMIT_CHOICES = ["不限时", "5", "10", "30", "60", "300", "600", "1800", "3600"]
ALG_CHOICES = [("自动（p-1 → rho）", "auto"), ("仅 Pollard rho", "rho"),
               ("仅 p-1", "pm1"), ("ECM 椭圆曲线", "ecm"),
               ("深度 p-1 → ECM → rho", "deep")]
THEMES = {
    "经典简洁": {
        "panel": "#f0f0f0", "fg": "#1a1a1a", "btn_bg": "#e8e8e8", "btn_fg": "#1a1a1a",
        "txt_bg": "#fcfcf8", "txt_fg": "#222222", "evt_bg": "#f3faf3", "evt_fg": "#333333",
        "live": "#2e7d32", "group": "#1a5fa8", "prime": "#c0392b",
        "hard": "#b9770e", "muted": "#8a8a8a", "dim": "#555555", "accent": "#1a5fa8",
    },
    "科幻炫酷": {
        "panel": "#0b1220", "fg": "#c8e6ff", "btn_bg": "#142848", "btn_fg": "#00e5ff",
        "txt_bg": "#0b1220", "txt_fg": "#c8e6ff", "evt_bg": "#0d1626", "evt_fg": "#9fd8ff",
        "live": "#00ff9d", "group": "#00e5ff", "prime": "#ff3366",
        "hard": "#ffb300", "muted": "#5f7fa6", "dim": "#5f7fa6", "accent": "#00e5ff",
    },
    "卡通二次元": {
        "panel": "#fff3f8", "fg": "#6a4a6a", "btn_bg": "#ffd6e8", "btn_fg": "#a03a6b",
        "txt_bg": "#fffafc", "txt_fg": "#5a4a6a", "evt_bg": "#fff0f7", "evt_fg": "#6a4a6a",
        "live": "#ff6fa5", "group": "#ff7bac", "prime": "#e0338c",
        "hard": "#f39c12", "muted": "#b0a0c0", "dim": "#a08aa8", "accent": "#ff7bac",
    },
}


class App:
    def __init__(self, root):
        self.root = root
        self.q = queue_mod.Queue()
        self.runner = None
        self.running = False
        self.runner_pids = []
        self._closing = False
        self._settings = self._load_settings()
        self.cpu_by_pid = {}          # pid -> 该进程 CPU%（监控线程写入，进度行读取）
        self._slots = {}
        self._next_seq = 0
        self._outstanding = 0

        ncpu = os.cpu_count() or 4

        root.title("大数分解可视化 · 每个数量级找出前 3 个质数（多进程并行版）")
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
                  wraplength=1150, justify="left").pack(fill="x")

        # 实时进度行：独立于结果文本区，每个数量级一行，行尾带“跳过”按钮
        livebar = ttk.Frame(root, padding=(10, 0))
        livebar.pack(side="bottom", fill="x")
        self.liveframe = tk.Frame(livebar, bg="#f0f0f0")
        self.liveframe.pack(fill="x")
        self._live_fg = "#2e7d32"
        self._panel = "#f0f0f0"
        self._btn_bg = "#e8e8e8"
        self._btn_fg = "#1a1a1a"

        top = ttk.Frame(root, padding=(10, 10, 10, 2))
        top.pack(fill="x")
        ttk.Label(top, text="输入 N：").pack(side="left")
        self.var_n = tk.StringVar(value="10^50")
        ent = ttk.Combobox(top, textvariable=self.var_n, width=25,
                           font=("Consolas", 11),
                           values=["10^12", "10^30", "10^50", "10^100", "10^200",
                                   "10^500", "2^64", "1e30", "123456789"])
        ent.pack(side="left", padx=(2, 8))
        ent.focus_set()
        ent.bind("<Return>", lambda _e: self.start())
        ttk.Label(top, text="每组限时:").pack(side="left")
        self.var_limit = tk.StringVar(value="10")
        ttk.Combobox(top, textvariable=self.var_limit, values=LIMIT_CHOICES,
                     width=6).pack(side="left", padx=(2, 8))
        ttk.Label(top, text="进程数:").pack(side="left")
        self.var_workers = tk.IntVar(value=ncpu)
        ttk.Spinbox(top, from_=1, to=max(ncpu, 1), increment=1,
                    textvariable=self.var_workers, width=4).pack(side="left", padx=(2, 8))
        ttk.Label(top, text="每组找质数:").pack(side="left")
        self.var_ppn = tk.IntVar(value=PRIMES_PER_GROUP)
        ttk.Spinbox(top, from_=1, to=20, increment=1,
                    textvariable=self.var_ppn, width=3).pack(side="left", padx=(2, 8))
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
        self.var_detail = tk.BooleanVar(value=False)
        ttk.Checkbutton(mid, text="列出合数明细（默认紧凑：只列质数+合数摘要）",
                        variable=self.var_detail).pack(side="left", padx=(14, 0))
        ttk.Label(mid, text="找因子算法:").pack(side="left", padx=(14, 0))
        self.var_alg = tk.StringVar(value=ALG_CHOICES[0][0])
        self.cmb_alg = ttk.Combobox(mid, textvariable=self.var_alg, width=16,
                                    values=[name for name, _v in ALG_CHOICES],
                                    state="readonly")
        self.cmb_alg.pack(side="left", padx=(2, 8))
        ttk.Label(mid, text="界面风格:").pack(side="left")
        self.var_theme = tk.StringVar(value=self._settings.get("theme", "经典简洁"))
        self.cmb_theme = ttk.Combobox(mid, textvariable=self.var_theme, width=10,
                                      values=list(THEMES.keys()), state="readonly")
        self.cmb_theme.pack(side="left", padx=(2, 0))
        self.cmb_theme.bind("<<ComboboxSelected>>", lambda _e: self.apply_theme())

        hint = ("程序会为每个数量级（个位、十位、百位…共 N 的位数个）找出前 3 个质数：从 10^k 起"
                "一个一个往上检查，途中遇到的合数也会按所选模式分解。默认只显示质数和合数总数，"
                "想看到每个数的分解过程就勾选「列出合数明细」。质数红色、没算完的橙色；"
                "每找到一个质数会记录在右侧「找到质数记录」面板里累积显示。"
                "输入框可下拉选择 10^50、2^64 等常用值，也可以直接粘贴整数。"
                "算得慢时，进度会实时显示在结果框下方的一行绿字区里（每个数量级一行，"
                "含正在算的数、该数已耗时、试除到哪个素数、所用进程）；「寻找因子」阶段用的是"
                "随机算法，可能耗时很久且无法准确估计剩余时间，等不到可点「跳过当前」；"
                "「暂停」会就地冻结正在算的组，「继续」恢复。")
        ttk.Label(root, text=hint, wraplength=1150, justify="left", foreground="#555",
                  padding=(12, 2)).pack(fill="x")

        body = ttk.Frame(root)
        body.pack(fill="both", expand=True, padx=10, pady=6)
        self._pw = ttk.Panedwindow(body, orient="horizontal")
        self._pw.pack(fill="both", expand=True)

        # 右侧：质数发现事件面板（不换行 + 横向滚动；中间分隔条可拖动调宽）
        evtframe = ttk.Frame(self._pw)
        ttk.Label(evtframe, text="找到质数记录（实时累积）", foreground="#2e7d32",
                  font=("Microsoft YaHei UI", 9, "bold")).pack(anchor="w")
        evt_vsb = ttk.Scrollbar(evtframe, orient="vertical")
        evt_hsb = ttk.Scrollbar(evtframe, orient="horizontal")
        self.evt = tk.Text(evtframe, width=72, font=("Consolas", 9), wrap="none",
                           state="disabled", bg="#f3faf3",
                           yscrollcommand=evt_vsb.set, xscrollcommand=evt_hsb.set)
        evt_vsb.configure(command=self.evt.yview)
        evt_hsb.configure(command=self.evt.xview)
        evt_hsb.pack(side="bottom", fill="x")
        evt_vsb.pack(side="right", fill="y")
        self.evt.pack(fill="both", expand=True)

        # 左侧：结果区
        txtframe = ttk.Frame(self._pw)
        hsb = ttk.Scrollbar(txtframe, orient="horizontal")
        vsb = ttk.Scrollbar(txtframe, orient="vertical")
        self.txt = tk.Text(txtframe, font=("Consolas", 10), wrap="none",
                           state="disabled", bg="#fcfcf8",
                           xscrollcommand=hsb.set, yscrollcommand=vsb.set)
        hsb.configure(command=self.txt.xview)
        vsb.configure(command=self.txt.yview)
        self._pw.add(txtframe, weight=4)
        self._pw.add(evtframe, weight=1)
        sash = self._settings.get("sash")
        if isinstance(sash, int) and sash >= 200:
            root.after(200, lambda: self._pw.sash_pos(0, sash))
        hsb.pack(side="bottom", fill="x")
        vsb.pack(side="right", fill="y")
        self.txt.pack(fill="both", expand=True)
        for tag, kw in TAGS.items():
            self.txt.tag_configure(tag, **kw)

        self.apply_theme()
        root.protocol("WM_DELETE_WINDOW", self._on_close)
        root.bind("<F9>", lambda _e: self.toggle_pause())
        root.bind("<F10>", lambda _e: self.skip_current())
        root.bind("<F11>", lambda _e: self.stop())
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
            raise ValueError("「每组限时」请选/填正整数秒，或选「不限时」")

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
        detail = bool(self.var_detail.get())
        try:
            ppn = min(max(int(self.var_ppn.get()), 1), 20)
        except Exception:
            ppn = PRIMES_PER_GROUP
        alg = dict(ALG_CHOICES).get(self.var_alg.get(), "auto")
        groups = len(str(N))
        if groups > 400 and not messagebox.askyesno(
                "确认",
                f"N 有 {groups} 位，将处理 {groups} 个数量级；数量级越大，找到 3 个质数\n"
                f"需要扫描的数越多（平均约 2.3×k 个），可能耗时非常久。确定继续吗？"):
            return
        self.running = True
        self._slots = {}
        self._next_seq = 0
        self._outstanding = 0
        self.txt.configure(state="normal")
        self.txt.delete("1.0", "end")
        self.txt.configure(state="disabled")
        self.evt.configure(state="normal")
        self.evt.delete("1.0", "end")
        self.evt.configure(state="disabled")
        mode_txt = "完整质因数分解" if mode == "full" else "只分解成两数相乘（证明是合数即可）"
        self._append(
            f"目标：每个数量级 10^k 从 10^k 起逐个检查，找出前 {ppn} 个质数"
            f"（途中合数也按模式分解，{'逐一列出' if detail else '折叠为组末摘要'}）\n"
            f"本次设置：N = {pretty_num(N, 80)}（{len(str(N))} 位）｜{mode_txt}｜找因子算法：{self.var_alg.get()}"
            f"{workers} 个进程｜每组限时 {'不限时' if limit is None else str(limit) + ' 秒'}\n"
            "怎么读结果：红色 = 质数；橙色 = 限时内没算完或已跳过；"
            "剩余大数「可能是质数，也可能是两个大质数的乘积」；\n"
            "　　　　　　大数用缩写：10^21 = 1 后面 21 个 0，10^21+1 = 10^21 加 1，5×10^103 = 5 后面 103 个 0。\n"
            + "─" * 78 + "\n", None)
        self.btn_start["state"] = "disabled"
        for b in (self.btn_pause, self.btn_stop):
            b["state"] = "normal"
        self.btn_pause["text"] = "暂停"
        self.btn_skip["state"] = "disabled"
        self.pbar.start(50)
        self.var_status.set(f"正在启动 {workers} 个计算进程…")
        self.runner = PoolRunner(N, limit, mode, workers, self.q, detail, ppn, alg)
        self.runner.cpu_by_pid = self.cpu_by_pid
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
        """跳过当前正在计算的所有组（F10）。"""
        if self.running and self.runner is not None:
            self.runner.skip_all()

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

    # ---------------- 主题 ----------------

    def _load_settings(self):
        try:
            import json
            with open(self._settings_path(), encoding="utf-8") as f:
                d = json.load(f)
            return d if isinstance(d, dict) else {}
        except Exception:
            return {}

    def _save_settings(self):
        try:
            import json
            d = dict(self._settings) if isinstance(self._settings, dict) else {}
            d["theme"] = self.var_theme.get()
            try:
                d["sash"] = int(self._pw.sash_pos(0))
            except Exception:
                pass
            with open(self._settings_path(), "w", encoding="utf-8") as f:
                json.dump(d, f)
        except Exception:
            pass

    def _settings_path(self):
        base = sys.executable if getattr(sys, "frozen", False) else __file__
        return os.path.join(os.path.dirname(os.path.abspath(base)), "分解工具设置.json")

    def _load_theme(self):
        try:
            import json
            with open(self._settings_path(), encoding="utf-8") as f:
                name = json.load(f).get("theme", "经典简洁")
            return name if name in THEMES else "经典简洁"
        except Exception:
            return "经典简洁"

    def apply_theme(self, *_args):
        """按所选风格（经典/科幻/二次元）给全部控件上色，并持久化选择。"""
        name = self.var_theme.get()
        th = THEMES.get(name, THEMES["经典简洁"])
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure(".", background=th["panel"], foreground=th["fg"],
                        fieldbackground=th["txt_bg"])
        style.configure("TFrame", background=th["panel"])
        style.configure("TLabel", background=th["panel"], foreground=th["fg"])
        style.configure("Dim.TLabel", background=th["panel"], foreground=th["dim"])
        style.configure("TButton", background=th["btn_bg"], foreground=th["btn_fg"],
                        padding=(8, 2))
        style.map("TButton",
                  background=[("disabled", th["panel"])],
                  foreground=[("disabled", th["muted"])])
        style.configure("TCheckbutton", background=th["panel"], foreground=th["fg"])
        style.configure("TRadiobutton", background=th["panel"], foreground=th["fg"])
        style.configure("TCombobox", fieldbackground=th["txt_bg"], foreground=th["fg"],
                        background=th["btn_bg"])
        style.configure("TSpinbox", fieldbackground=th["txt_bg"], foreground=th["fg"],
                        background=th["panel"], arrowcolor=th["fg"])
        style.configure("TProgressbar", troughcolor=th["txt_bg"], background=th["accent"])
        self.root.configure(bg=th["panel"])
        self.liveframe.configure(bg=th["panel"])
        self._panel = th["panel"]
        self._btn_bg = th["btn_bg"]
        self._btn_fg = th["btn_fg"]
        self._live_fg = th["live"]
        self.txt.configure(bg=th["txt_bg"], fg=th["txt_fg"],
                           insertbackground=th["txt_fg"])
        self.evt.configure(bg=th["evt_bg"], fg=th["evt_fg"],
                           insertbackground=th["evt_fg"])
        for tag, key in (("group", "group"), ("prime", "prime"),
                         ("hard", "hard"), ("muted", "muted")):
            self.txt.tag_configure(tag, foreground=th[key])
        self._save_settings()

    def _on_close(self):
        self._closing = True
        self._save_settings()
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
        self.txt.configure(state="disabled")

    def _evt_append(self, text):
        """右侧“找到质数记录”面板：累积追加，不覆盖。"""
        self.evt.configure(state="normal")
        self.evt.insert("end", text + "\n")
        self.evt.see("end")
        self.evt.configure(state="disabled")

    def _feed_slot(self, seq, content):
        self._slots[seq] = content
        while self._next_seq in self._slots:
            c = self._slots.pop(self._next_seq)
            if isinstance(c, tuple):
                c = [c]
            for text, tag in c:
                self._append(text, tag)
            self._next_seq += 1
        self.txt.see("end")

    def _update_progress(self, rows):
        """重建实时进度区：每个数量级一行，行尾带该组的“跳过”按钮。"""
        for w in self.liveframe.winfo_children():
            w.destroy()
        for seq, text in rows:
            row = tk.Frame(self.liveframe, bg=self._panel)
            row.pack(fill="x")
            tk.Label(row, text=text, anchor="w", justify="left",
                     bg=self._panel, fg=self._live_fg,
                     font=("Consolas", 10)).pack(side="left", fill="x", expand=True)
            if seq is not None:
                tk.Button(row, text="跳过", font=("Microsoft YaHei UI", 8),
                          bg=self._btn_bg, fg=self._btn_fg, relief="flat",
                          bd=0, padx=8, pady=1, cursor="hand2",
                          command=lambda s=seq: self.skip_one(s)
                          ).pack(side="right", padx=(6, 0))

    def skip_one(self, seq):
        """只跳过指定数量级。"""
        if self.running and self.runner is not None:
            self.runner.skip_one(seq)

    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "slot":
                    self._feed_slot(msg[1], msg[2])
                elif kind == "milestone":
                    self._evt_append(msg[1])
                elif kind == "progress_rows":
                    self._update_progress(msg[1])
                elif kind == "status":
                    self.var_status.set(msg[1])
                elif kind == "outstanding":
                    self._outstanding = msg[1]
                    if self.running:
                        self.btn_skip["state"] = "normal" if msg[1] > 0 else "disabled"
                elif kind == "sysinfo":
                    self.var_sys.set(msg[1])
                elif kind == "summary":
                    self.var_live.set("")
                    self._append(msg[1], None)
                    self._finish(msg[2])
                elif kind == "error":
                    self.var_live.set("")
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
                    d = max(0.0, t - prev_pid.get(pid, t))
                    cpu_dt += d
                    self.cpu_by_pid[pid] = d / 2.0 * 100.0   # 单核百分比
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
                busy = self.runner.busy_count() if self.runner is not None else 0
                busy_txt = f"（忙碌 {busy} · 空闲 {max(0, alive - 1 - busy)}）" if alive > 1 else ""
                ram = _ram_info()
                if ram:
                    load, total, avail = ram
                    ram_txt = f"内存 {_fmt_bytes(total)}（可用 {_fmt_bytes(avail)}，已用 {load}%）"
                else:
                    ram_txt = "内存信息不可用"
                text = (f"电脑：{get_cpu_name()}｜{ncpu} 线程｜{sys_txt}｜{ram_txt}\n"
                        f"本程序：{alive} 个进程{busy_txt} · CPU ≈{cores:.1f} 核"
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
    assert pretty_num(5 * 10 ** 103) == "5×10^103"          # 科学计数法去尾零
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
    # ECM 椭圆曲线分解
    random.seed(11)
    q1 = _next_prime(random.randrange(10 ** 5, 10 ** 6))
    q2 = _next_prime(random.randrange(10 ** 12, 10 ** 13))
    n_ecm = q1 * q2
    d = pollard_ecm(n_ecm, Ctl(stop_event=threading.Event(),
                               deadline=time.perf_counter() + 60))
    assert d in (q1, q2), (d, q1, q2)
    print(f"ECM OK：{d} 是 {n_ecm} 的因子")
    # 数量级扫描：找前 3 个质数
    rows, pf, scanned, stop = scan_magnitude(0, 10, "full", None)
    primes0 = [num for num, kind, *_ in rows if kind == "prime"]
    assert primes0 == [2, 3, 5] and stop is None, (primes0, pf, scanned, stop)
    rows, pf, scanned, stop = scan_magnitude(1, 10 ** 2, "full", None)
    primes1 = [num for num, kind, *_ in rows if kind == "prime"]
    assert primes1 == [11, 13, 17] and scanned == 8 and stop is None, (primes1, scanned)
    rows, pf, scanned, stop = scan_magnitude(2, 10 ** 3, "two", None)
    primes2 = [num for num, kind, *_ in rows if kind == "prime"]
    assert primes2 == [101, 103, 107] and stop is None, (primes2, scanned)
    # 每组质数个数可配置
    rows_p2, pf_p2, scanned_p2, stop_p2 = scan_magnitude(1, 10 ** 2, "full", None, False, 2)
    primes_p2 = [num for num, kind, *_ in rows_p2 if kind == "prime"]
    assert primes_p2 == [11, 13] and scanned_p2 == 4 and stop_p2 is None, (primes_p2, scanned_p2)
    header, lines, tail = render_group_lines(1, 10 ** 2, rows_p2, pf_p2,
                                             scanned_p2, None, False, 2)
    assert "找到前 2 个质数" in tail[0]
    print("数量级扫描 OK：10^0→[2,3,5]  10^1→[11,13,17]  10^2→[101,103,107]  每组质数个数可配")
    # 渲染：紧凑模式只列质数+合数摘要+耗时最长 3 个数；明细模式逐个列出
    header, lines, tail = render_group_lines(2, 10 ** 3, rows, 3, scanned, None, False)
    tags = [t for _l, t in lines]
    assert tags.count("prime") == 3 and tags.count("muted") == 2 and len(lines) == 5, (tags, len(lines))
    assert "另扫描合数 5 个" in lines[3][0], lines[3]
    top3_line = lines[4][0]
    assert "耗时最长的 3 个数" in top3_line and top3_line.count("用时") == 3, top3_line
    header_d, lines_d, tail_d = render_group_lines(2, 10 ** 3, rows, 3, scanned, None, True)
    assert len(lines_d) == scanned + 1 and sum(1 for _l, t in lines_d if t == "prime") == 3
    assert "耗时最长的 3 个数" in lines_d[-1][0]
    print("紧凑/明细渲染 OK")
    # 渲染对齐：数行的 = 与 用时 显示列一致（中文按 2 倍宽度；汇总行不参与对齐）
    header, lines, tail = render_group_lines(1, 10 ** 2, rows, 3, scanned, None, True)
    row_lines = [l for l, _t in lines if " = " in l]
    eq_cols = {disp_width(l.split(" = ")[0]) for l in row_lines}
    use_cols = {disp_width(l.split("用时")[0]) for l in row_lines}
    assert len(row_lines) == scanned and len(eq_cols) == 1 and len(use_cols) == 1, (eq_cols, use_cols)
    print("组内对齐 OK")
    # 限时路径：60 位半素数 1 秒内应超时
    random.seed(7)
    semi = (_next_prime(random.randrange(10 ** 29, 10 ** 30) | 1)
            * _next_prime(random.randrange(10 ** 29, 10 ** 30) | 1))
    try:
        factorize(semi, Ctl(stop_event=ev, deadline=time.perf_counter() + 1.0))
        raise AssertionError("60 位半素数应在限时内超时")
    except FactorTimeout as e:
        facs, rem = e.args
        plain = [r[0] if isinstance(r, tuple) else r for r in rem]
        assert not facs and plain == [semi], (facs, rem)
    print("限时超时路径 OK")
    # 跳过路径
    sk = threading.Event()
    sk.set()
    try:
        factorize(semi, Ctl(stop_event=threading.Event(), skip_event=sk, deadline=None))
        raise AssertionError("应触发跳过")
    except SkipRequested:
        pass
    print("跳过路径 OK")
    # 大数量级扫描 1 秒内应超时（未找满 3 个质数）
    rows, pf, scanned, stop = scan_magnitude(
        103, 10 ** 104, "full", Ctl(deadline=time.perf_counter() + 1.0))
    assert stop == "timeout" and pf < 3 and scanned > 0, (stop, pf, scanned)
    print("大数量级限时 OK")
    selftest_pool()
    selftest_skip_in_pool(semi)
    print("SELFTEST OK")


def selftest_pool():
    """多进程流水线：顺序、完整性、每组 3 个质数。"""
    N = 10 ** 3
    out_q = queue_mod.Queue()
    runner = PoolRunner(N, limit=10, mode="full", workers=4, out_q=out_q)
    runner.start()
    slots = {}
    nxt = 0
    total_primes = 0
    summary = None
    deadline = time.time() + 120
    while summary is None and time.time() < deadline:
        try:
            msg = out_q.get(timeout=1.0)
        except queue_mod.Empty:
            continue
        if msg[0] == "slot":
            slots[msg[1]] = msg[2]
            while nxt in slots:
                content = slots.pop(nxt)
                total_primes += sum(1 for _t, tag in content if tag == "prime")
                nxt += 1
        elif msg[0] == "summary":
            summary = msg
    runner.close()
    assert summary is not None, "流水线未在限时内完成"
    assert nxt == len(str(N)), (nxt, len(str(N)))     # 每个数量级一组
    # k=0,1,2 组各找到 3 个质数；k=3 组只有 1000 一个数（N=10^3），找不到质数
    assert total_primes == 9, total_primes
    print("多进程流水线（顺序+每组 3 质数）OK")


def _wait_group_result(result_q, timeout):
    """从结果队列取下一个 group 结果（跳过进度消息）。"""
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            msg = result_q.get(timeout=1.0)
        except queue_mod.Empty:
            continue
        if msg[0] == "result":
            return msg
    raise AssertionError("等待超时，未收到 group 结果")


def selftest_skip_in_pool(semi):
    """多进程中的跳过/停止：事件能打断不限时任务。"""
    ctx = multiprocessing.get_context("spawn")
    task_q = ctx.Queue()
    result_q = ctx.Queue()
    stop_ev = ctx.Event()
    skip_ev = ctx.Event()
    pause_ev = ctx.Event()
    p = ctx.Process(target=_pool_worker,
                    args=(task_q, result_q, stop_ev, skip_ev, pause_ev, 0))
    p.start()
    task_q.put((0, 1, 10 ** 40, None, "full", False, 3, "auto"))   # k=1 组：很快找满 3 个质数
    msg = _wait_group_result(result_q, 60)
    assert msg[3] == "group", msg
    # 不限时的大数量级组：k=500（1663 位），找 3 个质数平均要扫描上千个数、
    # 每个数试除上万次，短时间内不可能完成 → 只能靠跳过打断
    task_q.put((1, 500, 10 ** 501, None, "full", False, 3, "auto"))
    time.sleep(5.0)
    skip_ev.set()
    msg = _wait_group_result(result_q, 120)
    assert msg[3] == "group", msg
    payload = msg[4]
    _header, _lines, tail, pf, scanned = payload
    assert pf < 3 and scanned > 0, (pf, scanned)
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
    if "--detail" in sys.argv:
        app.var_detail.set(True)
    demo_val = next((a.split("=", 1)[1] for a in sys.argv
                     if a.startswith("--demo=")), "10^12" if "--demo" in sys.argv else None)
    if demo_val is not None:
        app.var_n.set(demo_val)
        root.after(800, app.start)   # 演示模式：自动开始
    root.mainloop()


if __name__ == "__main__":
    main()
