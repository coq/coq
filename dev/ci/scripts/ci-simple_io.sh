#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download simple_io

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/simple_io"
  dune build -p coq-simple-io @install
  dune install -p coq-simple-io --prefix=$CI_INSTALL_DIR
)
