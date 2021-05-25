#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download aac_tactics

( cd "${CI_BUILD_DIR}/aac_tactics"
  make
  make install
)
