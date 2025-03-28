#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'

cd _test

coqdep -f _CoqProject Loader.v -worker @ROCQWORKER@ > Loader.v.d.real

diff -u Loader.v.d.expected Loader.v.d.real
