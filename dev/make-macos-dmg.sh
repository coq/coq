#!/bin/bash

# Fail on first error
set -e

# Configuration setup
eval `opam config env`
make distclean
OUTDIR=$PWD/_install
DMGDIR=$PWD/_dmg
./configure -debug -prefix $OUTDIR
VERSION=$(sed -n -e '/^let coq_version/ s/^[^"]*"\([^"]*\)"$/\1/p' configure.ml)
APP=bin/CoqIDE_${VERSION}.app

# Create a .app file with CoqIDE
~/.local/bin/jhbuild run make -j -l2 $APP

# Build Coq and run test-suite
make && make check

# Add Coq to the .app file
make OLDROOT=$OUTDIR COQINSTALLPREFIX=$APP/Contents/Resources/ install-coq install-ide-toploop

# Sign the .app file
codesign -f -s - $APP

# Create the dmg bundle
mkdir -p $DMGDIR
ln -s /Applications $DMGDIR
cp -r $APP $DMGDIR
hdiutil create -imagekey zlib-level=9 -volname CoqIDE_$VERSION -srcfolder $DMGDIR -ov -format UDZO CoqIDE_$VERSION.dmg
