#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download mathcomp

( cd "${CI_BUILD_DIR}/mathcomp/mathcomp"
  make
  make test-suite
  make install
)
