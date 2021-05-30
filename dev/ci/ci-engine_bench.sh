#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download engine_bench

export COQEXTRAFLAGS='-native-compiler ondemand'
( cd "${CI_BUILD_DIR}/engine_bench"
  make coq
  make coq-perf-Sanity
)
