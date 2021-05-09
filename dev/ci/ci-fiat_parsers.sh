#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download fiat_parsers

ulimit -s
ulimit -s 65536
ulimit -s
( cd "${CI_BUILD_DIR}/fiat_parsers"
  make parsers parsers-examples
  make fiat-core
)
