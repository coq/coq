#!/bin/bash

set -e -x

APPVEYOR_OPAM_SWITCH=4.07.0+mingw64c

wget https://github.com/fdopen/opam-repository-mingw/releases/download/0.0.0.1/opam64.tar.xz
tar -xf opam64.tar.xz
bash opam64/install.sh

opam init -a mingw https://github.com/fdopen/opam-repository-mingw.git --comp $APPVEYOR_OPAM_SWITCH --switch $APPVEYOR_OPAM_SWITCH
eval "$(opam config env)"
opam install -y num ocamlfind camlp5 ounit

cd "$APPVEYOR_BUILD_FOLDER" && ./configure -local && make && make byte && make -C test-suite all INTERACTIVE= && make validate
