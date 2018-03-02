REM This script either runs the test suite with OPAM (if USEOPAM is true) or
REM builds the Coq binary packages for windows (if USEOPAM is false).

if %ARCH% == 32 (
  SET ARCHLONG=i686
  SET CYGROOT=C:\cygwin
  SET SETUP=setup-x86.exe
)

if %ARCH% == 64 (
  SET ARCHLONG=x86_64
  SET CYGROOT=C:\cygwin64
  SET SETUP=setup-x86_64.exe
)

SET CYGCACHE=%CYGROOT%\var\cache\setup
SET APPVEYOR_BUILD_FOLDER_MFMT=%APPVEYOR_BUILD_FOLDER:\=/%
SET APPVEYOR_BUILD_FOLDER_CFMT=%APPVEYOR_BUILD_FOLDER_MFMT:C:/=/cygdrive/c/%
SET DESTCOQ=C:\coq%ARCH%_inst
SET COQREGTESTING=Y

if %USEOPAM% == false (
  call %APPVEYOR_BUILD_FOLDER%\dev\build\windows\MakeCoq_MinGW.bat -threads=1 ^
    -arch=%ARCH% -installer=Y -coqver=%APPVEYOR_BUILD_FOLDER_CFMT% ^
    -destcyg=%CYGROOT% -destcoq=%DESTCOQ% -cygcache=%CYGCACHE% ^
    -addon=bignums -make=N ^
    -setup %CYGROOT%\%SETUP% || GOTO ErrorExit
  copy "%CYGROOT%\build\coq-local\dev\nsis\*.exe" dev\nsis || GOTO ErrorExit
  7z a coq-opensource-archive-windows-%ARCHLONG%.zip %CYGROOT%\build\tarballs\* || GOTO ErrorExit
)

if %USEOPAM% == true (
  %CYGROOT%\%SETUP% -qnNdO -R %CYGROOT% -l %CYGCACHE% -s %CYGMIRROR% ^
    -P rsync -P patch -P diffutils -P make -P unzip -P m4 -P findutils -P time
  %CYGROOT%/bin/bash -l %APPVEYOR_BUILD_FOLDER%/dev/ci/appveyor.sh || GOTO ErrorExit
)

GOTO :EOF

:ErrorExit
  ECHO ERROR %0 failed
  EXIT /b 1
