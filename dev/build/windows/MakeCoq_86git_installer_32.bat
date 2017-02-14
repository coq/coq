call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=32 ^
  -installer=Y ^
  -coqver=git-v8.6 ^
  -destcyg=%ROOTPATH%\cygwin_coq32_86git_inst ^
  -destcoq=%ROOTPATH%\coq32_86git_inst
