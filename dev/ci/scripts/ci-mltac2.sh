#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download mltac2

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/mltac2"
  dune build --root . --only-packages=rocq-mltac2 @install
  dune install --root . rocq-mltac2 --prefix="$CI_INSTALL_DIR"
)
