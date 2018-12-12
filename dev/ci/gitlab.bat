@ECHO OFF

REM This script builds and signs the Windows packages on Gitlab

ECHO "Start Time"
TIME /T

REM List currently used cygwin and target folders for debugging / maintenance purposes

ECHO "Currently used cygwin folders"
DIR C:\ci\cygwin*
ECHO "Currently used target folders"
DIR C:\ci\coq*
ECHO "Root folders"
DIR C:\

if %ARCH% == 32 (
  SET ARCHLONG=i686
  SET SETUP=setup-x86.exe
)

if %ARCH% == 64 (
  SET ARCHLONG=x86_64
  SET SETUP=setup-x86_64.exe
)

SET CYGROOT=C:\ci\cygwin%ARCH%
SET DESTCOQ=C:\ci\coq%ARCH%

CALL :MakeUniqueFolder %CYGROOT% CYGROOT
CALL :MakeUniqueFolder %DESTCOQ% DESTCOQ

powershell -Command "(New-Object Net.WebClient).DownloadFile('http://www.cygwin.com/%SETUP%', '%SETUP%')"
SET CYGCACHE=%CYGROOT%\var\cache\setup
SET CI_PROJECT_DIR_MFMT=%CI_PROJECT_DIR:\=/%
SET CI_PROJECT_DIR_CFMT=%CI_PROJECT_DIR_MFMT:C:/=/cygdrive/c/%
SET COQREGTESTING=Y
SET PATH=%PATH%;C:\Program Files\7-Zip\;C:\Program Files\Microsoft SDKs\Windows\v7.1\Bin

if exist %CYGROOT%\build\ rd /s /q %CYGROOT%\build
if exist %DESTCOQ%\ rd /s /q %DESTCOQ%

call %CI_PROJECT_DIR%\dev\build\windows\MakeCoq_MinGW.bat -threads=1 ^
  -arch=%ARCH% -installer=Y -coqver=%CI_PROJECT_DIR_CFMT% ^
  -destcyg=%CYGROOT% -destcoq=%DESTCOQ% -cygcache=%CYGCACHE% ^
  -addon=bignums ^
  -addon=equations ^
  -addon=ltac2 ^
  -addon=mtac2 ^
  -addon=mathcomp ^
  -addon=menhir ^
  -addon=menhirlib ^
  -addon=compcert ^
  -addon=extlib ^
  -addon=quickchick ^
  -addon=coquelicot ^
  -addon=vst ^
  -addon=aactactics ^
  -make=N ^
  -setup %CI_PROJECT_DIR%\%SETUP% || GOTO ErrorCopyLogFilesAndExit

ECHO "Start Artifact Creation"
TIME /T

mkdir artifacts

CALL :CopyLogFiles

copy "%CYGROOT%\build\coq-local\dev\nsis\*.exe" artifacts || GOTO ErrorExit
REM The open source archive is only required for release builds
IF DEFINED WIN_CERTIFICATE_PATH (
  7z a artifacts\coq-opensource-archive-windows-%ARCHLONG%.zip %CYGROOT%\build\tarballs\* || GOTO ErrorExit
) ELSE (
  REM In non release builds, create a dummy file
  ECHO "This is not a release build - open source archive not created / uploaded" > artifacts\coq-opensource-info.txt
)

REM DO NOT echo the signing command below, as this would leak secrets in the logs
IF DEFINED WIN_CERTIFICATE_PATH (
  IF DEFINED WIN_CERTIFICATE_PASSWORD (
    ECHO Signing package
    @signtool sign /f %WIN_CERTIFICATE_PATH% /p %WIN_CERTIFICATE_PASSWORD% dev\nsis\*.exe
    signtool verify /pa dev\nsis\*.exe
  )
)

ECHO "Finished Artifact Creation"
TIME /T

CALL :CleanupFolders

ECHO "Finished Cleanup"
TIME /T

GOTO :EOF

:CopyLogFiles
  ECHO Copy log files for artifact upload
  MKDIR artifacts\buildlogs
  COPY %CYGROOT%\build\buildlogs\* artifacts\buildlogs
  MKDIR artifacts\filelists
  COPY %CYGROOT%\build\filelists\* artifacts\filelists
  MKDIR artifacts\flagfiles
  COPY %CYGROOT%\build\flagfiles\* artifacts\flagfiles
  GOTO :EOF

:CleanupFolders
  ECHO "Cleaning %CYGROOT%"
  RMDIR /S /Q "%CYGROOT%"
  ECHO "Cleaning %DESTCOQ%"
  RMDIR /S /Q "%DESTCOQ%"
  GOTO :EOF

:MakeUniqueFolder
  REM Create a uniquely named folder
  REM This script is safe because folder creation is atomic - either we create it or fail
  REM %1 = base path or directory (_%RANDOM%_%RANDOM% is appended to this)
  REM %2 = name of the variable which receives the unique folder name
  SET "UNIQUENAME=%1_%RANDOM%_%RANDOM%"
  MKDIR "%UNIQUENAME%"
  IF ERRORLEVEL 1 GOTO :MakeUniqueFolder
  SET "%2=%UNIQUENAME%"
  GOTO :EOF

:ErrorCopyLogFilesAndExit
  CALL :CopyLogFiles
  REM fall through

:ErrorExit
  CALL :CleanupFolders
  ECHO ERROR %0 failed
  EXIT /b 1
