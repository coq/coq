#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

coq_makefile -f _CoqProject -o Makefile

make b.vo

[ -e a.vo ] && [ -e b.vo ]
