#!/usr/bin/env bash

set -e
export PATH=$COQBIN:$PATH
export LC_ALL=C

rm -rf _test
mkdir _test
cp _CoqProject _test/
cd _test
mkdir src

echo '{ let foo = () }' > src/file1.mlg
echo 'let bar = File1.foo' > src/file2.ml
coq_makefile -f _CoqProject -o Makefile
make src/file2.cmx
[ -f src/file2.cmx ]
