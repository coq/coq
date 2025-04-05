#!/usr/bin/env bash

set -e

export COQBIN="$BIN"
export PATH="$BIN:$PATH"

cd misc/tc_declaration_observer
rocq makefile -f _CoqProject -o Makefile
make clean
rm -f main.out
make
diff -u --strip-trailing-cr main.out main.out.reference
