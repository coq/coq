#!/usr/bin/env bash
a=$(uname)

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
make quick COQC=coqc_stm
# vio2vo is broken on Windows (#6720)
if [ "$a" = "Darwin" ] || [ "$a" = "Linux" ]; then
    make vio2vo J=2 COQC=coqc_stm
    test -f theories/test.vo
    make validate
fi
