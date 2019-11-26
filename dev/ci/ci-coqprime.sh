#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coqprime

( cd "${CI_BUILD_DIR}/coqprime" && make && make install)
