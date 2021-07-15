#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download kami

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/kami"
  make
  make install
)
