#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coq_performance_tests

( cd "${CI_BUILD_DIR}/coq_performance_tests"
  make_full coq perf-Sanity
  make validate
  make install
)
