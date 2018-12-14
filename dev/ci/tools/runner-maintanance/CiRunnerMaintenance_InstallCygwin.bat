@ECHO OFF

REM ========== COPYRIGHT/COPYLEFT ==========

REM (C) 2018 Intel Deutschland GmbH
REM Author: Michael Soegtrop

REM Released to the public by Intel under the
REM GNU Lesser General Public License Version 2.1 or later
REM See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

REM ========== NOTES ==========

REM This scripts sets up a cygwin environment suitable for CI runner maintenance

REM ========== DEFAULT VALUES FOR PARAMETERS ==========

REM For a description of all parameters, see ReadMe.md

SET BATCHFILE=%~0
SET BATCHDIR=%~dp0

REM see -arch in ReadMe.md, but values are x86_64 or i686 (not 64 or 32)
SET ARCH=x86_64

REM see -destcyg in ReadMe.md
SET DESTCYG=C:\bin\cygwin_ci_maintenance

REM see -setup in ReadMe.md
SET SETUP=setup-x86_64.exe

REM see -proxy in ReadMe.md
IF DEFINED HTTP_PROXY (
  SET PROXY=%HTTP_PROXY:http://=%
) else (
  REM One can't set a variable to empty in DOS, but you can set it to a space this way.
  REM The quotes are just there to make the space visible and to protect from "remove trailing spaces".
  SET "PROXY= "
)

REM see -cygrepo in ReadMe.md
SET CYGWIN_REPOSITORY=http://mirror.easyname.at/cygwin

REM see -cygcache in ReadMe.md
SET CYGWIN_LOCAL_CACHE_WFMT=%BATCHDIR%cygwin_cache

REM see -cyglocal in ReadMe.md
SET CYGWIN_FROM_CACHE=N

REM see -cygquiet in ReadMe.md
SET CYGWIN_QUIET=Y

REM ========== PARSE COMMAND LINE PARAMETERS ==========

SHIFT

:Parse

IF "%~0" == "-arch" (
  IF "%~1" == "32" (
    SET ARCH=i686
    SET SETUP=setup-x86.exe
  ) ELSE (
    IF "%~1" == "64" (
      SET ARCH=x86_64
      SET SETUP=setup-x86_64.exe
    ) ELSE (
      ECHO "Invalid -arch, valid are 32 and 64"
      GOTO :EOF
    )
  )
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-destcyg" (
  SET DESTCYG=%~1
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-setup" (
  SET SETUP=%~1
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-proxy" (
  SET PROXY=%~1
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-cygrepo" (
  SET CYGWIN_REPOSITORY=%~1
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-cygcache" (
  SET CYGWIN_LOCAL_CACHE_WFMT=%~1
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-cyglocal" (
  SET CYGWIN_FROM_CACHE=%~1
  CALL :CheckYN -cyglocal %~1 || GOTO ErrorExit
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-cygquiet" (
  SET CYGWIN_QUIET=%~1
  CALL :CheckYN -cygquiet %~1 || GOTO ErrorExit
  SHIFT
  SHIFT
  GOTO Parse
)

IF NOT "%~0" == "" (
  ECHO Install cygwin for CI runner maintenance
  ECHO !!! Illegal parameter %~0
  ECHO Usage:
  ECHO CiRunnerMaintenance_InstallCygwin
  CALL :PrintPars
  GOTO :EOF
)

REM ========== CONFIRM PARAMETERS ==========

CALL :PrintPars
REM Note: DOS batch replaces variables on parsing, so one can't use a variable just set in an () block
SET /p ANSWER="Is this correct? y/n "
IF NOT "%ANSWER%"=="y" (GOTO :EOF)

REM ========== DERIVED VARIABLES ==========

SET CYGWIN_INSTALLDIR_WFMT=%DESTCYG%
SET TARGET_ARCH=%ARCH%-w64-mingw32
SET BASH=%CYGWIN_INSTALLDIR_WFMT%\bin\bash

REM Convert pathes to various formats
REM WFMT = windows format (C:\..)          Used in this batch file.
REM CFMT = cygwin format (\cygdrive\c\..)  Used for Cygwin PATH varible, which is : separated, so C: doesn't work.
REM MFMT = MinGW format (C:/...)           Used for the build, because \\ requires escaping. Mingw can handle \ and /.

SET CYGWIN_INSTALLDIR_MFMT=%CYGWIN_INSTALLDIR_WFMT:\=/%
SET SOURCE_LOCAL_CACHE_MFMT=%SOURCE_LOCAL_CACHE_WFMT:\=/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_MFMT:C:/=/cygdrive/c/%
SET SOURCE_LOCAL_CACHE_CFMT=%SOURCE_LOCAL_CACHE_MFMT:C:/=/cygdrive/c/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_CFMT:D:/=/cygdrive/d/%
SET SOURCE_LOCAL_CACHE_CFMT=%SOURCE_LOCAL_CACHE_CFMT:D:/=/cygdrive/d/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_CFMT:E:/=/cygdrive/e/%
SET SOURCE_LOCAL_CACHE_CFMT=%SOURCE_LOCAL_CACHE_CFMT:E:/=/cygdrive/e/%

ECHO CYGWIN INSTALL DIR (WIN)    = %CYGWIN_INSTALLDIR_WFMT%
ECHO CYGWIN INSTALL DIR (MINGW)  = %CYGWIN_INSTALLDIR_MFMT%
ECHO CYGWIN INSTALL DIR (CYGWIN) = %CYGWIN_INSTALLDIR_CFMT%

REM WARNING: Add a space after the = in case you want set this to empty, otherwise the variable will be unset
SET MAKE_OPT=-j %MAKE_THREADS%

REM ========== DERIVED CYGWIN SETUP OPTIONS ==========

REM WARNING: Add a space after the = otherwise the variable will be unset
SET CYGWIN_OPT=

IF "%CYGWIN_FROM_CACHE%" == "Y" (
  SET CYGWIN_OPT= %CYGWIN_OPT% -L
)

IF "%CYGWIN_QUIET%" == "Y" (
  SET CYGWIN_OPT= %CYGWIN_OPT% -q --no-admin
)

ECHO ========== DOWNLOAD CYGWIN SETUP ==========

powershell -Command "(New-Object Net.WebClient).DownloadFile('http://www.cygwin.com/%SETUP%', '%BATCHDIR%\%SETUP%')"

ECHO ========== INSTALL CYGWIN ==========

REM Cygwin setup sets proper ACLs (permissions) for folders it CREATES.
REM Otherwise chmod won't work and e.g. the ocaml build will fail.
REM Cygwin setup does not touch the ACLs of existing folders.
REM => Create the setup log in a temporary location and move it later.

REM Get Unique temporary file name
:logfileloop
SET LOGFILE=%TEMP%\CygwinSetUp%RANDOM%-%RANDOM%-%RANDOM%-%RANDOM%.log
if exist "%LOGFILE%" GOTO logfileloop

REM Run Cygwin Setup

%BATCHDIR%\%SETUP% ^
  --proxy "%PROXY%" ^
  --site "%CYGWIN_REPOSITORY%" ^
  --root "%CYGWIN_INSTALLDIR_WFMT%" ^
  --local-package-dir "%CYGWIN_LOCAL_CACHE_WFMT%" ^
  --no-shortcuts ^
  %CYGWIN_OPT% ^
  -P wget,curl,nc,git,unzip,patch,diffutils,make,m4, ^
  -P perl,python ^
  -P bash-completion ^
  > "%LOGFILE%" ^
  || GOTO ErrorExit

MKDIR "%CYGWIN_INSTALLDIR_WFMT%\build"
MKDIR "%CYGWIN_INSTALLDIR_WFMT%\build\buildlogs"
MOVE  "%LOGFILE%" "%CYGWIN_INSTALLDIR_WFMT%\build\buildlogs\cygwinsetup.log" || GOTO ErrorExit

IF NOT "%CYGWIN_QUIET%" == "Y" (
  REM Like most setup programs, cygwin setup starts the real setup as a separate process, so wait for it.
  REM This is not required with the -cygquiet=Y and the resulting --no-admin option.
  :waitsetup
  tasklist /fi "imagename eq %SETUP%" | find ":" > NUL
  IF ERRORLEVEL 1 GOTO waitsetup
)

ECHO ========== CONFIGURE CYGWIN USER ACCOUNT ==========

REM In case this batch file is called from a cygwin bash (e.g. a git repo) we need to clear
REM HOME (otherwise we get to the home directory of the other installation)
REM PROFILEREAD (this is set to true if the /etc/profile has been read, which creates user)
SET "HOME="
SET "PROFILEREAD="

copy "%BATCHDIR%\CiRunnerMaintenance_ConfigureCygwinProfile.sh" "%CYGWIN_INSTALLDIR_WFMT%\var\tmp" || GOTO ErrorExit
%BASH% --login "%CYGWIN_INSTALLDIR_CFMT%\var\tmp\CiRunnerMaintenance_ConfigureCygwinProfile.sh" "%PROXY%" || GOTO ErrorExit

ECHO ========== FINISHED ==========

GOTO :EOF

ECHO ========== BATCH FUNCTIONS ==========

:PrintPars
  REM  01234567890123456789012345678901234567890123456789012345678901234567890123456789
  ECHO -arch     ^<i686 or x86_64^> Set cygwin to 32 or 64 bit
  ECHO -destcyg  ^<path to cygwin destination folder^>
  ECHO -setup    ^<cygwin setup program name^> (auto adjusted to -arch)
  ECHO -proxy    ^<internet proxy^>
  ECHO -cygrepo  ^<cygwin download repository^>
  ECHO -cygcache ^<local cygwin repository/cache^>
  ECHO -cyglocal ^<Y or N^> install cygwin from cache
  ECHO -cygquiet ^<Y or N^> install cygwin without user interaction
  ECHO(
  ECHO See ReadMe.md for a detailed description of all parameters
  ECHO(
  ECHO Parameter values (default or currently set):
  ECHO -arch     = %ARCH%
  ECHO -destcyg  = %DESTCYG%
  ECHO -setup    = %SETUP%
  ECHO -proxy    = %PROXY%
  ECHO -cygrepo  = %CYGWIN_REPOSITORY%
  ECHO -cygcache = %CYGWIN_LOCAL_CACHE_WFMT%
  ECHO -cyglocal = %CYGWIN_FROM_CACHE%
  ECHO -cygquiet = %CYGWIN_QUIET%
  GOTO :EOF

:CheckYN
  REM Reset errorlevel to 0
  CMD /c "EXIT /b 0"
  IF "%2" == "Y" (
    REM OK Y
  ) ELSE IF "%2" == "N" (
    REM OK N
  ) ELSE (
    ECHO ERROR Parameter %1 must be Y or N, but is %2
    GOTO ErrorExit
  )
  GOTO :EOF

:ErrorExit
  ECHO ERROR CiRunnerMaintenance_InstallCygwin.bat failed
  EXIT /b 1
