#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

WITH_SUBMODULES=1
git_download perennial

ulimit -s
ulimit -s 65536
ulimit -s
( cd "${CI_BUILD_DIR}/perennial"
  make TIMED=false lite
)
