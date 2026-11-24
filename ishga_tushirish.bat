@echo off
chcp 65001 >nul
cd /d "%~dp0"
title Davomat dashboard
python server.py
pause
