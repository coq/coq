#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download unimath

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/unimath" && make BUILD_COQ=no )
