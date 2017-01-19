call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -mode=absolute ^
  -ocaml=Y ^
  -make=Y ^
  -coqver=8.6rc1 ^
  -destcyg=%ROOTPATH%\cygwin_coq64_86rc1_abs ^
  -destcoq=%ROOTPATH%\coq64_86rc1_abs
