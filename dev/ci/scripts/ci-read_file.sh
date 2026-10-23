#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download read_file

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/read_file"
  dune build --root . --only-packages=rocq-read-file @install @runtest
  dune install --root . rocq-read-file --prefix="$CI_INSTALL_DIR"
)
