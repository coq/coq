#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download elpi

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/elpi"
  touch dune-workspace
  make build
  make install DUNE_install_FLAGS=--prefix="$CI_INSTALL_DIR"
)
