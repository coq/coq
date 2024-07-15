#!/usr/bin/env bash

. ../timing-template/init.sh

coq_makefile -f _CoqProject -o Makefile
make cleanall
make pretty-timed TGTS="all" -j1 || exit $?
