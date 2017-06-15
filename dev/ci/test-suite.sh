#!/usr/bin/env bash

set -ex

source dev/ci/exports.sh

get-artifact-coq-with-fallback

cd test-suite
make clean

# careful with the ending /
make -j ${NJOBS} BIN="$CI_INSTALL/bin/" LIB="$CI_INSTALL/lib/coq/" all
