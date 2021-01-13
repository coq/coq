#!/bin/bash

# Fail on first error
set -e

# Configuration setup
DMGDIR=$PWD/_dmg
VERSION=$(sed -n -e '/^let coq_version/ s/^[^"]*"\([^"]*\)"$/\1/p' configure.ml)
APP=bin/CoqIDE_${VERSION}.app

# Install Coq into the .app file
make OLDROOT="$OUTDIR" COQINSTALLPREFIX="$APP/Contents/Resources" install-coq install-ide-toploop

# Fill .app file with metadata and other .app specific stuff (like non-system .so)
make PRIVATEBINARIES="$APP" -j 1 -l2 "$APP" VERBOSE=1

# Create the dmg bundle
mkdir -p "$DMGDIR"
ln -sf /Applications "$DMGDIR/Applications"
cp -r "$APP" "$DMGDIR"

mkdir -p _build

# Temporary countermeasure to hdiutil error 5341
# head -c9703424 /dev/urandom > $DMGDIR/.padding

hdi_opts=(-volname "coq-$VERSION-installer-macos"
          -srcfolder "$DMGDIR"
          -ov # overwrite existing file
          -format UDZO
          -imagekey "zlib-level=9"

          # needed for backward compat since macOS 10.14 which uses APFS by default
          # see discussion in #11803
          -fs hfs+
         )
hdiutil create "${hdi_opts[@]}" "_build/coq-$VERSION-installer-macos.dmg"
