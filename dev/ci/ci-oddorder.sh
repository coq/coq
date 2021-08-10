#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download oddorder

( cd "${CI_BUILD_DIR}/oddorder"
  make
  make install
)
