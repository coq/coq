#!/usr/bin/env bash

set -e
export PATH=$COQBIN:$PATH
export LC_ALL=C

rm -rf _test
mkdir _test
cd _test

touch a.v
echo 'Require Test.a.' > b.v

printf '%s\n' "-R . Test" > _CoqProject
for x in a b c; do echo $x.v >> _CoqProject; done

coq_makefile -f _CoqProject -o Makefile

make b.vo
[ -f b.vo ]

if make; then false; fi
