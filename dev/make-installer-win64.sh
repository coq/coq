#!/bin/sh

set -e

NSIS="$BASE/NSIS/makensis"
ZIP=_make.zip
URL1=http://sourceforge.net/projects/gnuwin32/files/make/3.81/make-3.81-bin.zip/download
URL2=http://sourceforge.net/projects/gnuwin32/files/make/3.81/make-3.81-dep.zip/download

[ -e config/Makefile ] || ./configure -debug -prefix ./ -with-doc no
make -j2 coqide
mkdir -p bin32
cp bin/* bin32/
make clean
make archclean
( . ${BASE}_64/environ && ./configure -debug -prefix ./ -with-doc no && make -j2 && make ide/coqidetop.cmxs )
cp bin32/coqide* bin/
if [ ! -e bin/make.exe ]; then
  wget -O $ZIP $URL1 && 7z x $ZIP "bin/*"
  wget -O $ZIP $URL2 && 7z x $ZIP "bin/*"
  rm -rf $ZIP
fi
VERSION=`grep ^VERSION= config/Makefile | cut -d = -f 2`
cd dev/nsis
"$NSIS" -DVERSION=$VERSION -DGTK_RUNTIME="`cygpath -w $BASE`" -DARCH="win64" coq.nsi
echo Installer:
ls -h $PWD/*exe
cd ../..
