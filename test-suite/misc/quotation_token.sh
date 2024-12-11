#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/quotation_token/

if which cygpath >/dev/null 2>&1; then OCAMLFINDSEP=\;; else OCAMLFINDSEP=:; fi

rocq makefile -f _CoqProject -o Makefile

make clean

make src/quotation_plugin.cma

TMP=output.txt
rm -f $TMP

if make > $TMP 2>&1; then
  echo "should fail"
  rm $TMP
  exit 1
fi

if grep "File.*quotation.v., line 12, characters 6-30" $TMP; then
  exit 0
elif grep "File.*quotation.v" $TMP; then
  echo "wrong loc"
  exit 1
else
  echo "wrong error:"
  cat $TMP
  exit 1
fi
