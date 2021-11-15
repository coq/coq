#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download itauto

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQCOPTS='-native-compiler ondemand'
( cd "${CI_BUILD_DIR}/itauto"
  make
  make install
)
