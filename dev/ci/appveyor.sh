#!/bin/bash

set -e -x

APPVEYOR_OPAM_VARIANT=ocaml-variants.4.07.1+mingw64c
NJOBS=2

wget https://github.com/fdopen/opam-repository-mingw/releases/download/0.0.0.2/opam64.tar.xz -O opam64.tar.xz
tar -xf opam64.tar.xz
bash opam64/install.sh

opam init default -j $NJOBS -a -y "https://github.com/fdopen/opam-repository-mingw.git#opam2" -c $APPVEYOR_OPAM_VARIANT --disable-sandboxing
eval "$(opam env)"
opam install -j $NJOBS -y num ocamlfind ounit

# Full regular Coq Build
cd "$APPVEYOR_BUILD_FOLDER" && ./configure -local && make -j $NJOBS && make byte -j $NJOBS && make -j $NJOBS -C test-suite all INTERACTIVE= # && make validate
