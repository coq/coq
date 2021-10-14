#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

WITH_SUBMODULES=1
git_download argosy

( cd "${CI_BUILD_DIR}/argosy"
  make
)
