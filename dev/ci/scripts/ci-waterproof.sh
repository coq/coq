#!/usr/bin/env/ bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download waterproof

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/waterproof"
  dune build -p coq-waterproof
  dune install -p coq-waterproof --prefix=$CI_INSTALL_DIR
)
