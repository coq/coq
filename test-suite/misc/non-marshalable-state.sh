#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd non-marshalable-state/

if which cygpath >/dev/null 2>&1; then OCAMLFINDSEP=\;; else OCAMLFINDSEP=:; fi
export OCAMLPATH=$PWD$OCAMLFINDSEP$OCAMLPATH

coq_makefile -f _CoqProject -o Makefile

make clean

make src/evil_plugin.cmxs
make src/good_plugin.cmxs

RC=1
# must fail
coqc -async-proofs on  -I src -Q theories Marshal theories/evil.v 2> log1 1>&2 || RC=0
#   for this reason
grep -q 'Marshalling error' log1 || RC=1

# must work
coqc -async-proofs off -I src -Q theories Marshal theories/evil.v

# must work
coqc -async-proofs on  -I src -Q theories Marshal theories/good.v


exit $RC
