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
