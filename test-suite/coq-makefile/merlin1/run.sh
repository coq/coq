#!/bin/sh

#set -x
set -e

export PATH=../../../bin/:$PATH
git clean -dfx .
coq_makefile -f _CoqProject -o Makefile
make .merlin
echo B $PWD/src > desired
echo S $PWD/src >> desired
tail -2 .merlin > actual
exec diff -u desired actual
