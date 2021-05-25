#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download elpi

( cd "${CI_BUILD_DIR}/elpi"
  make
  make install
)

git_download hierarchy_builder

( cd "${CI_BUILD_DIR}/hierarchy_builder"
  make
  make install
)
