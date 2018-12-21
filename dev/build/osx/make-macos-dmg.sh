#!/bin/bash

# Fail on first error
set -e

# TODO use Docker instead of this
brew update
brew unlink python
brew install opam gnu-time gtk+ expat gtksourceview gdk-pixbuf
brew unlink python@2
brew link python3
pip3 install macpack
opam init -a -y -j 2 --compiler=ocaml-base-compiler.4.07.1 default https://opam.ocaml.org
opam switch ocaml-base-compiler.4.07.1
eval $(opam config env)
opam update
opam config list
opam list
opam install -j 2 -y camlp5 ocamlfind.1.8.0 num lablgtk.2.18.6 conf-gtksourceview.2
rm -rf ~/.opam/log/
opam list

# Configuration setup
OUTDIR=$PWD/_install
DMGDIR=$PWD/_dmg
VERSION=$(sed -n -e '/^let coq_version/ s/^[^"]*"\([^"]*\)"$/\1/p' configure.ml)
APP=bin/CoqIDE_${VERSION}.app

make clean
./configure -native-compiler no -coqide opt -prefix "$OUTDIR"
make -j "$NJOBS" byte
make -j "$NJOBS" world
make test-suite/misc/universes/all_stdlib.v
make -j "$NJOBS" world
make install
make install-byte

# Create a .app file with CoqIDE, without signing it
make PRIVATEBINARIES="$APP" -j "$NJOBS" -l2 "$APP"

# Add Coq to the .app file
make OLDROOT="$OUTDIR" COQINSTALLPREFIX="$APP/Contents/Resources/" install-coq install-ide-toploop

if [ -n "$MACOS_CERTIFICATE_IDENTITY" ] && [ -n "$MACOS_CERTIFICATE_PASSWORD" ] && [ -n "$MACOS_CERTIFICATE_BASE_PATH" ]
then
    readonly KEYCHAIN=macos-build.keychain
    # This pile of hacks is required to avoid having to manually validate access to the key through UI
    security create-keychain -p gitlab "${KEYCHAIN}"
    security default-keychain -s "${KEYCHAIN}"
    security unlock-keychain -p gitlab "${KEYCHAIN}"
    security set-keychain-settings -t 3600 -u "${KEYCHAIN}"
    security import "${MACOS_CERTIFICATE_BASE_PATH}/foundation.cer" -k ~/Library/Keychains/"${KEYCHAIN}" -T /usr/bin/codesign
    security import "${MACOS_CERTIFICATE_BASE_PATH}/foundation.p12" -k ~/Library/Keychains/"${KEYCHAIN}" -P "${MACOS_CERTIFICATE_PASSWORD}" -T /usr/bin/codesign
    security set-key-partition-list -S apple-tool:,apple: -s -k gitlab ~/Library/Keychains/"${KEYCHAIN}"
    codesign -f -v -s "$MACOS_CERTIFICATE_IDENTITY" "$APP"
    security default-keychain -s "login.keychain"
    security delete-keychain "${KEYCHAIN}"
fi

# Create the dmg bundle
mkdir -p "$DMGDIR"
ln -sf /Applications "$DMGDIR/Applications"
cp -r "$APP" "$DMGDIR"

mkdir -p _build

# Temporary countermeasure to hdiutil error 5341
# head -c9703424 /dev/urandom > $DMGDIR/.padding

hdiutil create -imagekey zlib-level=9 -volname "coq-$VERSION-installer-macos" -srcfolder "$DMGDIR" -ov -format UDZO "_build/coq-$VERSION-installer-macos.dmg"
