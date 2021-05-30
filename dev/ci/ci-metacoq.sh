#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download metacoq

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/metacoq"
  ./configure.sh local
  make .merlin
  make ci-local
  make install
)
