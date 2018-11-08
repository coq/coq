#!/bin/bash
set -e
set -o pipefail
export PATH="$COQBIN:$PATH"

# Clean
rm -f *.vo *.vos *.vok *.glob *.aux Makefile

# Test building all vos, then all vok
coq_makefile -R . TEST -o Makefile *.v
make vos
make vok

# Cleanup
make clean

# Test using compilation in custom order
set -x #echo on
coqc A.v
coqc -vos B.v
coqc -vos C.v
coqc -vok B.v
coqc -vok C.v
