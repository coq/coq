#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download engine_bench

( cd "${CI_BUILD_DIR}/engine_bench" && make coq && make coq-perf-Sanity )
