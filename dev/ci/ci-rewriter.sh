#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download rewriter

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

ulimit -s
ulimit -s 65536
ulimit -s
( cd "${CI_BUILD_DIR}/rewriter"
  make
  make install
)
