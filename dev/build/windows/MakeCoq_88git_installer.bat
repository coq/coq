@ECHO OFF

REM ========== COPYRIGHT/COPYLEFT ==========

REM (C) 2016 Intel Deutschland GmbH
REM Author: Michael Soegtrop

REM Released to the public by Intel under the
REM GNU Lesser General Public License Version 2.1 or later
REM See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

REM ========== BUILD COQ ==========

call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -installer=Y ^
  -coqver=git-v8.8 ^
  -destcyg=%ROOTPATH%\cygwin_coq64_88_inst ^
  -destcoq=%ROOTPATH%\coq64_88_inst ^
  -addon=bignums

IF %ERRORLEVEL% NEQ 0 (
  ECHO MakeCoq_88git_installer.bat failed with error code %ERRORLEVEL%
  EXIT /b %ERRORLEVEL%
)
