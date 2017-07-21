#!/usr/bin/env bash

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
make
exec make validate
