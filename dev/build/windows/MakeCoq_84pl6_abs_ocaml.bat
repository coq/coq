call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -mode=absolute ^
  -ocaml=Y ^
  -make=Y ^
  -coqver=8.4pl6 ^
  -destcyg=%ROOTPATH%\cygwin_coq64_84pl6_abs ^
  -destcoq=%ROOTPATH%\coq64_84pl6_abs
