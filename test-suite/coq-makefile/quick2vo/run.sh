#!/usr/bin/env bash

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
make quick2vo J=2
test -f theories/test.vo
make validate
