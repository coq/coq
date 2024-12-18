#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

# -vos/-vok not compatible with async proofs
export COQEXTRAFLAGS="$COQEXTRAFLAGS -async-proofs off"

# Test building all vos, then all vok
rocq makefile -f _CoqProject -o Makefile
make vos
make vok

# Cleanup
make clean

# Test using compilation in custom order
set -x #echo on
rocq c A.v
rocq c -vos B.v
rocq c -vos C.v
rocq c -vok B.v
rocq c -vok C.v
