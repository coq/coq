#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download riscv_coq

( cd "${CI_BUILD_DIR}/riscv_coq"
  make all EXTERNAL_DEPENDENCIES=1
  make install
)
