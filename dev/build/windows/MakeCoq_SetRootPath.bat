REM ========== COPYRIGHT/COPYLEFT ==========

REM (C) 2016 Intel Deutschland GmbH
REM Author: Michael Soegtrop

REM Released to the public by Intel under the
REM GNU Lesser General Public License Version 2.1 or later
REM See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

REM ========== CHOOSE A SENSIBLE ROOT PATH ==========

@ ECHO OFF

REM Figure out a root path for coq and cygwin

REM For the \nul trick for testing folders see
REM https://support.microsoft.com/en-us/kb/65994

IF EXIST D:\bin\nul (
  SET ROOTPATH=D:\bin
) else if EXIST C:\bin (
  SET ROOTPATH=C:\bin
) else (
  SET ROOTPATH=C:
)

ECHO ROOTPATH set to %ROOTPATH%
