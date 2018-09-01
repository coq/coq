#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download bignums

( cd "${CI_BUILD_DIR}/bignums" && make && make install)
