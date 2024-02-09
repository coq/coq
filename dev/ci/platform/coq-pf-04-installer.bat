REM build the installer artifact

REM XXX: make this a variable with the branch name
cd platform-*

REM XXX: This is redundant with the previous scripts, we could centralize it
REM In fact, the variable is only needed to access bash
SET CYGROOT=C:\ci\cygwin%ARCH%
SET BASH=%CYGROOT%\bin\bash

MKDIR %GITHUB_WORKSPACE%\artifacts

%BASH% --login -c "pwd && ls -la && cd /platform && windows/create_installer_windows.sh" || GOTO ErrorExit

REM Output is in cygwin home; in general the script has a bit of a
REM mess in terms of using the GITHUB_WORKSPACE sometimes, and the
REM CYGWIN home some others. I use the path here directly as to avoid
REM issues with quoting, which in the previous script required some
REM really obscure code.
COPY /v /b %CYGROOT%\platform\windows_installer\*.exe %GITHUB_WORKSPACE%\artifacts || GOTO ErrorExit

GOTO :EOF

:ErrorExit
  ECHO ERROR %0 failed
  EXIT /b 1
