#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download deriving

( cd "${CI_BUILD_DIR}/deriving" && make && make tests && make install )
