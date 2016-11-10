call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -mode=absolute ^
  -ocaml=Y ^
  -make=Y ^
  -coqver=git-v8.6 ^
  -destcyg=%ROOTPATH%\cygwin_coq64_86git_abs ^
  -destcoq=%ROOTPATH%\coq64_86git_abs
