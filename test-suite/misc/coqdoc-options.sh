#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/coqdoc-options/

rocq makefile -f _CoqProject -o Makefile

make clean

make html

diff -u --strip-trailing-cr html/Coqdoc.test.html 15933.html.out
