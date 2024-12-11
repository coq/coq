#!/usr/bin/env bash

. ../timing-template/init.sh

rocq makefile -f _CoqProject -o Makefile
make cleanall
make pretty-timed TGTS="all" -j1 || exit $?
