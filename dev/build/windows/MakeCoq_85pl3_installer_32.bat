call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=32 ^
  -installer=Y ^
  -coqver=8.5pl3 ^
  -destcyg=%ROOTPATH%\cygwin_coq32_85pl3_inst ^
  -destcoq=%ROOTPATH%\coq32_85pl3_inst
