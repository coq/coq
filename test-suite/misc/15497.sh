#!/usr/bin/env bash

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

(cd misc/15497; coq_makefile -R . Top A.v B.v -o Makefile; make all html)
diff -u --strip-trailing-cr misc/15497/B.glob.out misc/15497/B.glob
R=$?
if [ $R == 0 ]; then
  exit 0
else
  exit 1
fi

