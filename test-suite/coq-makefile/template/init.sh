#!/bin/sh
. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'

cd _test || exit 1
mkdir -p src
mkdir -p theories/sub

cp ../../template/theories/sub/testsub.v theories/sub
cp ../../template/theories/test.v theories
cp ../../template/src/test.ml4 src
cp ../../template/src/test_aux.mli src
cp ../../template/src/test.mli src
cp ../../template/src/test_plugin.mlpack src
cp ../../template/src/test_aux.ml src
