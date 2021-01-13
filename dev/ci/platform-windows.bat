REM @ECHO OFF

REM SET ARCH=64
REM SET PLATFORM=https://github.com/coq/platform/archive/v8.13.zip
REM SET CI_PROJECT_DIR=C:\root

REM This script builds a minimal Windows platform on Gitlab

ECHO "Start Time"
TIME /T

REM List currently used cygwin and target folders for debugging / maintenance purposes

ECHO "Currently used cygwin folders"
DIR C:\ci\cygwin*
ECHO "Currently used target folders"
DIR C:\ci\coq*
ECHO "Root folders"
DIR C:\
ECHO "Powershell version"
powershell -Command "Get-Host"
ECHO "Git installation of Mingw"
DIR "C:\Program Files\Git\mingw64\bin\*.exe"

ECHO "--------- START -------"

SET CYGROOT=C:\ci\cygwin%ARCH%
SET CYGCACHE=C:\ci\cache\cgwin

CALL :MakeUniqueFolder %CYGROOT% CYGROOT

SET CI_PROJECT_DIR_MFMT=%CI_PROJECT_DIR:\=/%
SET CI_PROJECT_DIR_CFMT=%CI_PROJECT_DIR_MFMT:C:/=/cygdrive/c/%
SET COQREGTESTING=y
SET PATH=%PATH%;C:\Program Files\7-Zip;C:\Program Files\Git\mingw64\bin


ECHO "Downloading %PLATFORM%"
curl -L -o platform.zip "%PLATFORM%"
7z x platform.zip

cd platform-*

call coq_platform_make_windows.bat ^
  -arch=%ARCH% ^
  -destcyg=%CYGROOT% ^
  -cygcache=%CYGCACHE% ^
  -extent=i ^
  -parallel=p ^
  -jobs=2 ^
  -switch=d || GOTO ErrorCopyLogFilesAndExit

cd ..

SET BASH=%CYGROOT%\bin\bash

ECHO "Start Artifact Creation"
TIME /T

MKDIR %CI_PROJECT_DIR%\artifacts
%BASH% --login -c "cd coq-platform && windows/create_installer_windows.sh && cp windows_installer/*.exe %CI_PROJECT_DIR_CFMT%/artifacts" || GOTO ErrorCopyLogFilesAndExit
TIME /T

CALL :CopyLogFiles

ECHO "Finished Artifact Creation"
TIME /T

CALL :CleanupFolders

ECHO "Finished Cleanup"
TIME /T

GOTO :EOF

:CopyLogFiles
  ECHO Copy log files for artifact upload
  REM This is currently not supported by the opam based build scripts
  GOTO :EOF

:CleanupFolders
  ECHO "Cleaning %CYGROOT%"
  RMDIR /S /Q "%CYGROOT%"
  GOTO :EOF

:MakeUniqueFolder
  REM Create a uniquely named folder
  REM This script is safe because folder creation is atomic - either we create it or fail
  REM %1 = base path or directory (_%RANDOM%_%RANDOM% is appended to this)
  REM %2 = name of the variable which receives the unique folder name
  SET "UNIQUENAME=%1_%RANDOM%_%RANDOM%"
  MKDIR "%UNIQUENAME%"
  IF ERRORLEVEL 1 GOTO :MakeUniqueFolder
  RMDIR "%UNIQUENAME%"
  SET "%2=%UNIQUENAME%"
  GOTO :EOF

:ErrorCopyLogFilesAndExit
  CALL :CopyLogFiles
  REM fall through

:ErrorExit
  CALL :CleanupFolders
  ECHO ERROR %0 failed
  EXIT /b 1
