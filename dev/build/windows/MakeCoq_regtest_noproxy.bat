REM ========== COPYRIGHT/COPYLEFT ==========

REM (C) 2016 Intel Deutschland GmbH
REM Author: Michael Soegtrop

REM Released to the public by Intel under the
REM GNU Lesser General Public License Version 2.1 or later
REM See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

REM ========== BUILD COQ ==========

call MakeCoq_SetRootPath

SET HTTP_PROXY=
SET HTTPS_PROXY=
MKDIR C:\Temp\srccache

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -mode=absolute ^
  -ocaml=Y ^
  -make=Y ^
  -coqver 8.5pl2 ^
  -srccache C:\Temp\srccache ^
  -cygquiet=Y ^
  -destcyg   %ROOTPATH%\cygwin_coq64_85pl2_abs ^
  -destcoq   %ROOTPATH%\coq64_85pl2_abs

pause
