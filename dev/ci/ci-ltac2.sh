#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download ltac2

( cd "${CI_BUILD_DIR}/ltac2" && make && make tests && make install )
