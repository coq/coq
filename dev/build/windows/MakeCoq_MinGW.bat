@ECHO OFF

REM ========== COPYRIGHT/COPYLEFT ==========

REM (C) 2016 Intel Deutschland GmbH
REM Author: Michael Soegtrop

REM Released to the public by Intel under the
REM GNU Lesser General Public License Version 2.1 or later
REM See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

REM ========== NOTES ==========

REM For Cygwin setup command line options
REM see https://cygwin.com/faq/faq.html#faq.setup.cli

REM ========== DEFAULT VALUES FOR PARAMETERS ==========

REM For a description of all parameters, see ReadMe.txt

SET BATCHFILE=%~0
SET BATCHDIR=%~dp0

REM see -arch in ReadMe.txt, but values are x86_64 or i686 (not 64 or 32)
SET ARCH=x86_64

REM see -mode in ReadMe.txt
SET INSTALLMODE=absolute

REM see -installer in ReadMe.txt
SET MAKEINSTALLER=N

REM see -ocaml in ReadMe.txt
SET INSTALLOCAML=N

REM see -make in ReadMe.txt
SET INSTALLMAKE=N

REM see -destcyg in ReadMe.txt
SET DESTCYG=C:\bin\cygwin_coq

REM see -destcoq in ReadMe.txt
SET DESTCOQ=C:\bin\coq

REM see -setup in ReadMe.txt
SET SETUP=setup-x86_64.exe

REM see -proxy in ReadMe.txt
IF DEFINED HTTP_PROXY (
  SET PROXY=%HTTP_PROXY:http://=%
) else (
  REM One can't set a variable to empty in DOS, but you can set it to a space this way.
  REM The quotes are just there to make the space visible and to protect from "remove trailing spaces".
  SET "PROXY= "
)

REM see -cygrepo in ReadMe.txt
SET CYGWIN_REPOSITORY=http://mirror.easyname.at/cygwin

REM see -cygcache in ReadMe.txt
SET CYGWIN_LOCAL_CACHE_WFMT=%BATCHDIR%cygwin_cache

REM see -cyglocal in ReadMe.txt
SET CYGWIN_FROM_CACHE=N

REM see -cygquiet in ReadMe.txt
SET CYGWIN_QUIET=Y

REM see -srccache in ReadMe.txt
SET SOURCE_LOCAL_CACHE_WFMT=%BATCHDIR%source_cache

REM see -coqver in ReadMe.txt
SET COQ_VERSION=8.5pl3

REM see -gtksrc in ReadMe.txt
SET GTK_FROM_SOURCES=N

REM see -threads in ReadMe.txt
SET MAKE_THREADS=8

REM see -addon in ReadMe.txt
SET "COQ_ADDONS= "

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

IF "%~0" == "-mode" (
  IF "%~1" == "mingwincygwin" (
    SET INSTALLMODE=%~1
  ) ELSE (
    IF "%~1" == "absolute" (
      SET INSTALLMODE=%~1
    ) ELSE (
      IF "%~1" == "relocatable" (
        SET INSTALLMODE=%~1
      ) ELSE (
        ECHO "Invalid -mode, valid are mingwincygwin, absolute and relocatable"
        GOTO :EOF
      )
    )
  )
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-installer" (
  SET MAKEINSTALLER=%~1
  CALL :CheckYN -installer %~1 || GOTO ErrorExit
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-ocaml" (
  SET INSTALLOCAML=%~1
  CALL :CheckYN -installer %~1 || GOTO ErrorExit
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-make" (
  SET INSTALLMAKE=%~1
  CALL :CheckYN -installer %~1 || GOTO ErrorExit
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

IF "%~0" == "-destcoq" (
  SET DESTCOQ=%~1
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

IF "%~0" == "-srccache" (
  SET SOURCE_LOCAL_CACHE_WFMT=%~1
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-coqver" (
  SET COQ_VERSION=%~1
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-gtksrc" (
  SET GTK_FROM_SOURCES=%~1
  CALL :CheckYN -gtksrc %~1 || GOTO ErrorExit
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-threads" (
  SET MAKE_THREADS=%~1
  SHIFT
  SHIFT
  GOTO Parse
)

IF "%~0" == "-addon" (
  SET "COQ_ADDONS=%COQ_ADDONS% %~1"
  SHIFT
  SHIFT
  GOTO Parse
)


IF NOT "%~0" == "" (
  ECHO Install cygwin and download, compile and install OCaml and Coq for MinGW
  ECHO !!! Illegal parameter %~0
  ECHO Usage:
  ECHO MakeCoq_MinGW
  CALL :PrintPars
  GOTO :EOF
)

IF NOT EXIST %SETUP% (
  ECHO The cygwin setup program %SETUP% doesn't exist. You must download it from https://cygwin.com/install.html.
  ECHO If the setup is in a different folder, set the full path to %SETUP% using the -setup option.
  GOTO :EOF
)

REM ========== ADJUST PARAMETERS ==========

IF "%INSTALLMODE%" == "mingwincygwin" (
  SET DESTCOQ=%DESTCYG%\usr\%ARCH%-w64-mingw32\sys-root\mingw
)

IF "%MAKEINSTALLER%" == "Y" (
  SET INSTALLMODE=relocatable
)

REM ========== CONFIRM PARAMETERS ==========

CALL :PrintPars
REM Note: DOS batch replaces variables on parsing, so one can't use a variable just set in an () block
IF "%COQREGTESTING%"=="Y" (GOTO DontAsk)
  SET /p ANSWER="Is this correct? y/n "
  IF NOT "%ANSWER%"=="y" (GOTO :EOF)
:DontAsk

REM ========== DERIVED VARIABLES ==========

SET CYGWIN_INSTALLDIR_WFMT=%DESTCYG%
SET RESULT_INSTALLDIR_WFMT=%DESTCOQ%
SET TARGET_ARCH=%ARCH%-w64-mingw32
SET BASH=%CYGWIN_INSTALLDIR_WFMT%\bin\bash

REM Convert pathes to various formats
REM WFMT = windows format (C:\..)          Used in this batch file.
REM CFMT = cygwin format (\cygdrive\c\..)  Used for Cygwin PATH varible, which is : separated, so C: doesn't work.
REM MFMT = MinGW format (C:/...)           Used for the build, because \\ requires escaping. Mingw can handle \ and /.

SET CYGWIN_INSTALLDIR_MFMT=%CYGWIN_INSTALLDIR_WFMT:\=/%
SET RESULT_INSTALLDIR_MFMT=%RESULT_INSTALLDIR_WFMT:\=/%
SET SOURCE_LOCAL_CACHE_MFMT=%SOURCE_LOCAL_CACHE_WFMT:\=/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_MFMT:C:/=/cygdrive/c/%
SET RESULT_INSTALLDIR_CFMT=%RESULT_INSTALLDIR_MFMT:C:/=/cygdrive/c/%
SET SOURCE_LOCAL_CACHE_CFMT=%SOURCE_LOCAL_CACHE_MFMT:C:/=/cygdrive/c/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_CFMT:D:/=/cygdrive/d/%
SET RESULT_INSTALLDIR_CFMT=%RESULT_INSTALLDIR_CFMT:D:/=/cygdrive/d/%
SET SOURCE_LOCAL_CACHE_CFMT=%SOURCE_LOCAL_CACHE_CFMT:D:/=/cygdrive/d/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_CFMT:E:/=/cygdrive/e/%
SET RESULT_INSTALLDIR_CFMT=%RESULT_INSTALLDIR_CFMT:E:/=/cygdrive/e/%
SET SOURCE_LOCAL_CACHE_CFMT=%SOURCE_LOCAL_CACHE_CFMT:E:/=/cygdrive/e/%

ECHO CYGWIN INSTALL DIR (WIN)    = %CYGWIN_INSTALLDIR_WFMT%
ECHO CYGWIN INSTALL DIR (MINGW)  = %CYGWIN_INSTALLDIR_MFMT%
ECHO CYGWIN INSTALL DIR (CYGWIN) = %CYGWIN_INSTALLDIR_CFMT%
ECHO RESULT INSTALL DIR (WIN)    = %RESULT_INSTALLDIR_WFMT%
ECHO RESULT INSTALL DIR (MINGW)  = %RESULT_INSTALLDIR_MFMT%
ECHO RESULT INSTALL DIR (CYGWIN) = %RESULT_INSTALLDIR_CFMT%

REM WARNING: Add a space after the = in case you want set this to empty, otherwise the variable will be unset
SET MAKE_OPT=-j %MAKE_THREADS%

REM ========== DERIVED CYGWIN SETUP OPTIONS ==========

REM One can't set a variable to empty in DOS, but you can set it to a space this way.
REM The quotes are just there to make the space visible and to protect from "remove trailing spaces".
SET "CYGWIN_OPT= "

IF "%CYGWIN_FROM_CACHE%" == "Y" (
  SET CYGWIN_OPT= %CYGWIN_OPT% -L
)

IF "%CYGWIN_QUIET%" == "Y" (
  SET CYGWIN_OPT= %CYGWIN_OPT% -q --no-admin
)

IF "%GTK_FROM_SOURCES%"=="N" (
  SET CYGWIN_OPT= %CYGWIN_OPT% -P mingw64-%ARCH%-gtk2.0,mingw64-%ARCH%-gtksourceview2.0
)

REM Cygwin setup sets proper ACLs (permissions) for folders it CREATES.
REM Otherwise chmod won't work and e.g. the ocaml build will fail.
REM Cygwin setup does not touch the ACLs of existing folders.

REM Run Cygwin Setup

SET RUNSETUP=Y
IF EXIST "%CYGWIN_INSTALLDIR_WFMT%\etc\setup\installed.db" (
  SET RUNSETUP=N
)
IF NOT "%CYGWIN_QUIET%" == "Y" (
  SET RUNSETUP=Y
)

IF "%COQREGTESTING%" == "Y" (
  ECHO "========== REMOVE EXISTING CYGWIN =========="
  DEL /S /F /Q "%CYGWIN_INSTALLDIR_WFMT%" > NUL
  SET RUNSETUP=Y
)

SET "EXTRAPACKAGES= "

IF NOT "%APPVEYOR%" == "True" (
  SET EXTRAPACKAGES=-P wget,curl,git,gcc-core,gcc-g++,automake1.5
)

ECHO "========== INSTALL CYGWIN =========="

IF "%RUNSETUP%"=="Y" (
  %SETUP% ^
    --proxy "%PROXY%" ^
    --site "%CYGWIN_REPOSITORY%" ^
    --root "%CYGWIN_INSTALLDIR_WFMT%" ^
    --local-package-dir "%CYGWIN_LOCAL_CACHE_WFMT%" ^
    --no-shortcuts ^
    %CYGWIN_OPT% ^
    -P make,unzip ^
    -P gdb,liblzma5 ^
    -P patch,automake1.14 ^
    -P mingw64-%ARCH%-binutils,mingw64-%ARCH%-gcc-core,mingw64-%ARCH%-gcc-g++,mingw64-%ARCH%-pkg-config,mingw64-%ARCH%-windows_default_manifest ^
    -P mingw64-%ARCH%-headers,mingw64-%ARCH%-runtime,mingw64-%ARCH%-pthreads,mingw64-%ARCH%-zlib ^
    -P libiconv-devel,libunistring-devel,libncurses-devel ^
    -P gettext-devel,libgettextpo-devel ^
    -P libglib2.0-devel,libgdk_pixbuf2.0-devel ^
    -P libfontconfig1 ^
    -P gtk-update-icon-cache ^
    -P libtool,automake ^
    -P intltool ^
    %EXTRAPACKAGES% ^
    || GOTO ErrorExit

  MKDIR "%CYGWIN_INSTALLDIR_WFMT%\build"
  MKDIR "%CYGWIN_INSTALLDIR_WFMT%\build\buildlogs"
)

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

copy "%BATCHDIR%\configure_profile.sh" "%CYGWIN_INSTALLDIR_WFMT%\var\tmp" || GOTO ErrorExit
%BASH% --login "%CYGWIN_INSTALLDIR_CFMT%\var\tmp\configure_profile.sh" "%PROXY%" || GOTO ErrorExit

ECHO ========== BUILD COQ ==========

MKDIR "%CYGWIN_INSTALLDIR_WFMT%\build"
MKDIR "%CYGWIN_INSTALLDIR_WFMT%\build\patches"

COPY "%BATCHDIR%\makecoq_mingw.sh" "%CYGWIN_INSTALLDIR_WFMT%\build" || GOTO ErrorExit
COPY "%BATCHDIR%\patches_coq\*.*" "%CYGWIN_INSTALLDIR_WFMT%\build\patches" || GOTO ErrorExit

%BASH% --login "%CYGWIN_INSTALLDIR_CFMT%\build\makecoq_mingw.sh" || GOTO ErrorExit

ECHO ========== FINISHED ==========

GOTO :EOF

ECHO ========== BATCH FUNCTIONS ==========

:PrintPars
  REM  01234567890123456789012345678901234567890123456789012345678901234567890123456789
  ECHO -arch     ^<i686 or x86_64^> Set cygwin, ocaml and coq to 32 or 64 bit
  ECHO -mode     ^<mingwincygwin = install coq in default cygwin mingw sysroot^>
  ECHO           ^<absoloute = install coq in -destcoq absulute path^>
  ECHO           ^<relocatable = install relocatable coq in -destcoq path^>
  ECHO -installer^<Y or N^> create a windows installer (will be in /build/coq/dev/nsis)
  ECHO -ocaml    ^<Y or N^> install OCaml in Coq folder (Y) or just in cygwin folder (N)
  ECHO -make     ^<Y or N^> install GNU Make in Coq folder (Y) or not (N)
  ECHO -destcyg  ^<path to cygwin destination folder^>
  ECHO -destcoq  ^<path to coq destination folder (mode=absoloute/relocatable)^>
  ECHO -setup    ^<cygwin setup program name^> (auto adjusted to -arch)
  ECHO -proxy    ^<internet proxy^>
  ECHO -cygrepo  ^<cygwin download repository^>
  ECHO -cygcache ^<local cygwin repository/cache^>
  ECHO -cyglocal ^<Y or N^> install cygwin from cache
  ECHO -cygquiet ^<Y or N^> install cygwin without user interaction
  ECHO -srccache ^<local source code repository/cache^>
  ECHO -coqver   ^<Coq version to install^>
  ECHO -gtksrc   ^<Y or N^> build GTK ^(90 min^) or use cygwin version
  ECHO -threads  ^<1..N^> Number of make threads
  ECHO -addon    ^<name^>  Enable building selected addon (can be repeated)
  ECHO(
  ECHO See ReadMe.txt for a detailed description of all parameters
  ECHO(
  ECHO Parameter values (default or currently set):
  ECHO -arch     = %ARCH%
  ECHO -mode     = %INSTALLMODE%
  ECHO -ocaml    = %INSTALLOCAML%
  ECHO -installer= %MAKEINSTALLER%
  ECHO -make     = %INSTALLMAKE%
  ECHO -destcyg  = %DESTCYG%
  ECHO -destcoq  = %DESTCOQ%
  ECHO -setup    = %SETUP%
  ECHO -proxy    = %PROXY%
  ECHO -cygrepo  = %CYGWIN_REPOSITORY%
  ECHO -cygcache = %CYGWIN_LOCAL_CACHE_WFMT%
  ECHO -cyglocal = %CYGWIN_FROM_CACHE%
  ECHO -cygquiet = %CYGWIN_QUIET%
  ECHO -srccache = %SOURCE_LOCAL_CACHE_WFMT%
  ECHO -coqver   = %COQ_VERSION%
  ECHO -gtksrc   = %GTK_FROM_SOURCES%
  ECHO -threads  = %MAKE_THREADS%
  ECHO -addon    = %COQ_ADDONS%
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
  ECHO ERROR MakeCoq_MinGW.bat failed
  EXIT /b 1
