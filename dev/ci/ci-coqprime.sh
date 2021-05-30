#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coqprime

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/coqprime"
  make
  make install
)
