#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download category_theory

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/category_theory"
  make
  make install
)
