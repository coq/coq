#!/bin/bash
set -e
set -o pipefail
# export COQBIN=../../bin
export PATH="$COQBIN:$PATH"

# requires "make coqlight coqbinaries tools"
# can be interrupted after compilation of the prelude

checker() { # give as argument the name of the output and expected output
  diff -q -a -u --strip-trailing-cr $1 $2 >&1 || exit 1
}

# Clean before start
rm -f *.vo *.vos *.vok *.glob *.aux Makefile Makefile.conf *.out.real

# Test building all vos, then all vok, for A and B and C files.
coq_makefile -R . TEST -o Makefile A.v B.v C.v
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

# Test whether Print Assumption is correctly disabled in -vos and -vok
# ../../bin/coqc -vok PrintAssumptions.v &> PrintAssumptions.out.real

coqc -vos PrintAssumptions.v
coqc -vok PrintAssumptions.v &> PrintAssumptions.out.real
checker PrintAssumptions.out PrintAssumptions.out.real

# Test Print Assumptions in plain compilation
# coqc A.v
# coqc B.v
# coqc C.v
# coqc PrintAssumptions.v
