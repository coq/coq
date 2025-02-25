#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/analysis"
  make -C reals_stdlib
  make -C reals_stdlib install
  make -C analysis_stdlib
  make -C analysis_stdlib install
)
