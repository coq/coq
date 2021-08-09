#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download tlc

( cd "${CI_BUILD_DIR}/tlc"
  make
  make install
)
