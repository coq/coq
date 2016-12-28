call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -mode=absolute ^
  -ocaml=Y ^
  -make=Y ^
  -coqver=8.5pl2 ^
  -destcyg=%ROOTPATH%\cygwin_coq64_85pl2_abs ^
  -destcoq=%ROOTPATH%\coq64_85pl2_abs
