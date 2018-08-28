#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download ext_lib

( cd "${CI_BUILD_DIR}/ext_lib" && make && make install)
