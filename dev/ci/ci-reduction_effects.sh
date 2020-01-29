#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download reduction_effects

( cd "${CI_BUILD_DIR}/reduction_effects" && make && make test && make install)
