#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/quotation_token/

coq_makefile -f _CoqProject -o Makefile

make clean

make src/quotation_plugin.cma

TMP=`mktemp`

if make > $TMP 2>&1; then
  echo "should fail"
  rm $TMP
  exit 1
fi

if grep "File.*quotation.v., line 12, characters 6-30" $TMP; then
  rm $TMP
  exit 0
else
  echo "wong loc: `grep File.*quotation.v $TMP`"
  rm $TMP
  exit 1
fi
