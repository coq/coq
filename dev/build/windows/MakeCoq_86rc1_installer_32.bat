call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=32 ^
  -installer=Y ^
  -coqver=8.6rc1 ^
  -destcyg=%ROOTPATH%\cygwin_coq32_86rc1_inst ^
  -destcoq=%ROOTPATH%\coq32_86rc1_inst
