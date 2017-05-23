#!/bin/sh

#set -x
set -e

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
make only TGTS="src/test.cmi src/test_aux.cmi" -j2
test -f src/test.cmi
test -f src/test_aux.cmi
! test -f src/test.cmo
