REM Print some debug information

ECHO "Root folders"
DIR C:\
ECHO "Powershell version"
powershell -Command "Get-Host"
ECHO "Git installation of Mingw"
DIR "C:\Program Files\Git\mingw64\bin\*.exe"
