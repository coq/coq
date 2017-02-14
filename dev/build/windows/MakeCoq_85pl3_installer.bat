call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -installer=Y ^
  -coqver=8.5pl3 ^
  -destcyg=%ROOTPATH%\cygwin_coq64_85pl3_inst ^
  -destcoq=%ROOTPATH%\coq64_85pl3_inst
