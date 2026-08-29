@echo off
rem 双击启动：大数分解可视化工具（优先使用打包好的 exe）
if exist "%~dp0大数分解工具.exe" (
    start "" "%~dp0大数分解工具.exe"
    exit /b
)
where pythonw >nul 2>nul
if %errorlevel%==0 (
    start "" pythonw "%~dp0factor_gui.py"
) else (
    start "" python "%~dp0factor_gui.py"
)
