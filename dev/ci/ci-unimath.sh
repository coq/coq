#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download unimath

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/unimath"
  # Bicategories consumes too much memory for the shared workers when -j 2
  sed -i.bak 's|Bicategories||' Makefile
  make BUILD_COQ=no
  mv Makefile.bak Makefile
  make BUILD_COQ=no -j 1
)
