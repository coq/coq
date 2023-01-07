#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/coqdoc-options/

coq_makefile -f _CoqProject -o Makefile

make clean

make html
