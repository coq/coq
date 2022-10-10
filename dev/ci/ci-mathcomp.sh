#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download mathcomp

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/mathcomp/mathcomp"
  make
  make install
)
