#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coq_record_update

( cd "${CI_BUILD_DIR}/coq_record_update"
  make
  make install
)
