call MakeCoq_SetRootPath

SET HTTP_PROXY=
EXPORT HTTP_PROXY=
MKDIR C:\Temp\srccache

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -mode=absolute ^
  -ocaml=Y ^
  -make=Y ^
  -coqver 8.5pl2 ^
  -srccache C:\Temp\srccache ^
  -cygquiet=Y ^
  -destcyg   %ROOTPATH%\cygwin_coq64_85pl2_abs ^
  -destcoq   %ROOTPATH%\coq64_85pl2_abs

pause