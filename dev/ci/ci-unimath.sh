#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download unimath

( cd "${CI_BUILD_DIR}/unimath" && make BUILD_COQ=no )
