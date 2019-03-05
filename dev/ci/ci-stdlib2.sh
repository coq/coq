#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download stdlib2

( cd "${CI_BUILD_DIR}/stdlib2/src" && ./bootstrap && make && make install)
