#!/usr/bin/env bash

set -e

. ../template/init.sh

mv theories/sub theories2

coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
make

cp ../_CoqProject.sub theories2/_CoqProject
cd theories2
coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
make
