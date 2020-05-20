#!/bin/sh
. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'

cd _test || exit 1
mkdir -p src
mkdir -p theories/sub

cp_file() {
  local _TARGET=$1
  cp ../../template/$_TARGET $_TARGET
  chmod u+w $_TARGET
}

# We chmod +w as to fix the case where the sources are read-only, as
# for example when using Dune's cache.
cp_file theories/sub/testsub.v
cp_file theories/test.v
cp_file src/test.mlg
cp_file src/test_aux.mli
cp_file src/test.mli
cp_file src/test_plugin.mlpack
cp_file src/test_aux.ml
