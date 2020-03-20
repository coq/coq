#!/usr/bin/env bash

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/quotation_token/

coq_makefile -f _CoqProject -o Makefile

make clean

make src/quotation_plugin.cma

TMP=`mktemp`

if which ocamlopt >/dev/null 2>&1; then
  echo "detected native code"
  if make > $TMP 2>&1; then
    echo "should fail"
    rm $TMP
    exit 1
  fi
else
  echo "detected byte-code"
  if OPT=-byte make > $TMP 2>&1; then
    echo "should fail"
    rm $TMP
    exit 1
  fi
fi

if grep "File.*quotation.v., line 12, characters 6-30" $TMP; then
  rm $TMP
  exit 0
else
  echo "wrong loc: `grep File.*quotation.v $TMP`"
  rm $TMP
  exit 1
fi
