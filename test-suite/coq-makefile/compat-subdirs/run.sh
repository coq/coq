#!/bin/sh

#set -x
set -e

export PATH=../../../bin/:$PATH
git clean -dfx .
coq_makefile -f _CoqProject -o Makefile
make
exec test -f "subdir/done"
