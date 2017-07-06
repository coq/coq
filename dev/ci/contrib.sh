#!/usr/bin/env bash

set -ex

source dev/ci/exports.sh

get-artifact-coq-with-fallback

# considering this just calls one of the ci-* scripts maybe we should skip the Makefile?
fold-start "Starting tests..." "coq.test"
make -f Makefile.ci -j ${NJOBS} ${TEST_TARGET}
fold-end "Tests done." "coq.test"
