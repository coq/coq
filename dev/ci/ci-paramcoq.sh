#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download paramcoq

# Typically flaky on our worker configuration
# https://gitlab.com/coq/coq/-/jobs/1144081161
export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/paramcoq" && make && make install && cd test-suite && make examples)
