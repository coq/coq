#!/bin/bash
set -e -x
wget $opam_url
tar -xf opam64.tar.xz
bash opam64/install.sh
opam init -a mingw https://github.com/fdopen/opam-repository-mingw.git --comp 4.02.3+mingw64c --switch 4.02.3+mingw64c
eval $(opam config env)
opam install -y ocamlfind camlp5
