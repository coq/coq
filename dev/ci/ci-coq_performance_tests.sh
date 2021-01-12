#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coq_performance_tests

# run make -k; make again if make fails so that the failing file comes last, so that it's easier to find the error messages in the CI log
function make_full() {
    if ! make -k "$@"; then make -k "$@"; exit 1; fi
}

( cd "${CI_BUILD_DIR}/coq_performance_tests" && make_full coq perf-Sanity && make validate && make install )
