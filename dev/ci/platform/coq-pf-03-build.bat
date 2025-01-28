REM Build the platform

SET CYGROOT=C:\ci\cygwin%ARCH%
SET CYGCACHE=C:\ci\cache\cgwin

REM Try CYGWIN_QUIET, but still this stage is super verbose
SET CYGWIN_QUIET=y

SET COQREGTESTING=y

REM XXX: make this a variable with the branch name
cd platform-*

call coq_platform_make_windows.bat ^
  -arch=%ARCH% ^
  -pick=ci ^
  -destcyg=%CYGROOT% ^
  -cygcache=%CYGCACHE% ^
  -extent=i ^
  -parallel=p ^
  -jobs=2 ^
  -switch=d ^
  -set-switch=y ^
  -override-dev-pkg="rocq-runtime=%GITHUB_SERVER_URL%/%GITHUB_REPOSITORY%/archive/%GITHUB_SHA%.tar.gz" ^
  -override-dev-pkg="rocq-core=%GITHUB_SERVER_URL%/%GITHUB_REPOSITORY%/archive/%GITHUB_SHA%.tar.gz" ^
  -override-dev-pkg="rocq-prover=%GITHUB_SERVER_URL%/%GITHUB_REPOSITORY%/archive/%GITHUB_SHA%.tar.gz" ^
  -override-dev-pkg="coq-core=%GITHUB_SERVER_URL%/%GITHUB_REPOSITORY%/archive/%GITHUB_SHA%.tar.gz" ^
  -override-dev-pkg="coq=%GITHUB_SERVER_URL%/%GITHUB_REPOSITORY%/archive/%GITHUB_SHA%.tar.gz" ^
  -override-dev-pkg="coqide-server=%GITHUB_SERVER_URL%/%GITHUB_REPOSITORY%/archive/%GITHUB_SHA%.tar.gz" ^
  -override-dev-pkg="rocqide=%GITHUB_SERVER_URL%/%GITHUB_REPOSITORY%/archive/%GITHUB_SHA%.tar.gz" ^
  || GOTO ErrorExit

GOTO :EOF

:ErrorExit
  ECHO ERROR %0 failed
  EXIT /b 1
