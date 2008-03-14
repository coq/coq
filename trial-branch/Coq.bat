@echo off
set COQBIN=%~0\..\bin
set COQLIB=%~0\..\lib
echo Using COQBIN= %COQBIN%
echo and   COQLIB= %COQLIB%
echo Starting Coq
%~0\..\bin\coqtop.opt.exe
pause