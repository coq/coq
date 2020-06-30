#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coq_performance_tests

( cd "${CI_BUILD_DIR}/coq_performance_tests" && make coq perf-Sanity && make validate && make install )
