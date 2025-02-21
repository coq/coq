#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download json

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/json"
  dune build -p coq-json @install
  dune install -p coq-json --prefix=$CI_INSTALL_DIR
)
