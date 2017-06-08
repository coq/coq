REM ========== COPYRIGHT/COPYLEFT ==========

REM (C) 2016 Intel Deutschland GmbH
REM Author: Michael Soegtrop

REM Released to the public by Intel under the
REM GNU Lesser General Public License Version 2.1 or later
REM See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

REM ========== RUN REGRESSION TESTS FOR COQ BUILD SCRIPTS ==========

SET COQREGTESTING=Y

REM Current stable
call MakeCoq_86git_abs_ocaml.bat || GOTO Error
call MakeCoq_86git_installer.bat || GOTO Error
call MakeCoq_86git_installer_32.bat || GOTO Error

REM Old but might still be used
call MakeCoq_85pl3_abs_ocaml.bat || GOTO Error
call MakeCoq_84pl6_abs_ocaml.bat || GOTO Error

REM Special variants, e.g. for debugging
call MakeCoq_86git_abs_ocaml_gtksrc.bat || GOTO Error
call MakeCoq_local_installer.bat || GOTO Error
call MakeCoq_explicitcachefolders_installer.bat || GOTO Error

REM Bleeding edge
call MakeCoq_trunk_installer.bat || GOTO Error

ECHO MakeCoq_regtests.bat: All tests finished successfully
GOTO :EOF

:Error
ECHO MakeCoq_regtests.bat failed with error code %ERRORLEVEL%
EXIT /b %ERRORLEVEL%
