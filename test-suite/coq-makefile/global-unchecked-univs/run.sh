#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

rocq makefile -f _CoqProject -o Makefile

export COQEXTRAFLAGS='-native-compiler no' # loading flags not supported by separate native compiler
make
