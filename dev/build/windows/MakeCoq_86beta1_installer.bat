call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -installer=Y ^
  -coqver=8.6beta1 ^
  -destcyg=%ROOTPATH%\cygwin_coq64_86beta1_inst ^
  -destcoq=%ROOTPATH%\coq64_86beta1_inst
