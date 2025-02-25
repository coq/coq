#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download analysis

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/analysis"
  make -C classical
  make -C classical install
  make -C reals
  make -C reals install
  make -C theories
  make -C theories install
  make -C experimental_reals
  make -C experimental_reals install
)
