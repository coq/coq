#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd side-eff-leak-univs/

coq_makefile -f _CoqProject -o Makefile

make clean

make src/evil_plugin.cma

if make; then
    >&2 echo 'Should have failed!'
    exit 1
fi
