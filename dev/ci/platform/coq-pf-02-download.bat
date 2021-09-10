REM Download platform script

SET PATH=%PATH%;C:\Program Files\7-Zip;C:\Program Files\Git\mingw64\bin

ECHO "Downloading %PLATFORM%"
curl -L -o platform.zip "%PLATFORM%"
7z x platform.zip
