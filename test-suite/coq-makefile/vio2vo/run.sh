#!/usr/bin/env bash
a=$(uname)

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
make quick
# vio2vo is broken on Windows (#6720)
if [ "$a" = "Darwin" ] || [ "$a" = "Linux" ]; then
    make vio2vo J=2
    test -f theories/test.vo
    make validate
fi
