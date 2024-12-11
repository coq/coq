#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

set -x
rocq makefile -Q . Top foo.v -o Makefile
make printvo
diff -u printvo.expected printvo || exit $?
