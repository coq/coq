#!/usr/bin/env bash

set -ex

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/non-marshalable-state/

if which cygpath >/dev/null 2>&1; then OCAMLFINDSEP=\;; else OCAMLFINDSEP=:; fi

rocq makefile -f _CoqProject -o Makefile

make clean

make src/evil_plugin.cmxs
make src/good_plugin.cmxs

if rocq c -async-proofs on  -I src -Q theories Marshal theories/evil.v 2> log1 1>&2; then
  >&2 echo "evil.v should have failed with async proofs on"
  exit 1
fi
if ! grep -q 'Marshalling error' log1; then
  >&2 echo "Missing expected error message in evil.v output"
  exit 1
fi

rocq c -async-proofs off -I src -Q theories Marshal theories/evil.v

rocq c -async-proofs on  -I src -Q theories Marshal theories/good.v
