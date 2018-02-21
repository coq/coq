#!/bin/bash

# Fail on first error
set -e

# Configuration setup
OUTDIR=$PWD/_install
DMGDIR=$PWD/_dmg
VERSION=$(sed -n -e '/^let coq_version/ s/^[^"]*"\([^"]*\)"$/\1/p' configure.ml)
APP=bin/CoqIDE_${VERSION}.app

# Create a .app file with CoqIDE, without signing it
make PRIVATEBINARIES="$APP" -j "$NJOBS" -l2 "$APP"

# Add Coq to the .app file
make OLDROOT="$OUTDIR" COQINSTALLPREFIX="$APP/Contents/Resources/" install-coq install-ide-toploop

# Create the dmg bundle
mkdir -p "$DMGDIR"
ln -sf /Applications "$DMGDIR/Applications"
cp -r "$APP" "$DMGDIR"

mkdir -p _build

# Temporary countermeasure to hdiutil error 5341
# head -c9703424 /dev/urandom > $DMGDIR/.padding

hdiutil create -imagekey zlib-level=9 -volname "coq-$VERSION-installer-macos" -srcfolder "$DMGDIR" -ov -format UDZO "_build/coq-$VERSION-installer-macos.dmg"
