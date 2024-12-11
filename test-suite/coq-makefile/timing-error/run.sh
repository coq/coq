#!/usr/bin/env bash

. ../timing-template/init.sh

rocq makefile -f _CoqProject -o Makefile
make cleanall
if make pretty-timed TGTS="all" -j1; then
    echo "Error: make pretty-timed should have failed"
    exit 1
fi
