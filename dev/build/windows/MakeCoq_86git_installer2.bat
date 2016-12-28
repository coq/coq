call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -installer=Y ^
  -coqver=git-v8.6 ^
  -destcyg=%ROOTPATH%\cygwin_coq64_86git_inst2 ^
  -destcoq=%ROOTPATH%\coq64_86git_inst2
