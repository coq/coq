#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download simple_io

( cd "${CI_BUILD_DIR}/simple_io" && make build && make install)
