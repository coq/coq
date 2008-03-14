@echo off
set COQBIN=%~0\..\bin
set COQLIB=%~0\..\lib
echo Using COQBIN= %COQBIN%
echo and   COQLIB= %COQLIB%
echo Starting Coqide
%~0\..\bin\coqide.opt.exe