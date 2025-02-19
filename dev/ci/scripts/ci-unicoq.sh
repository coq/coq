#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download unicoq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/unicoq"
  coq_makefile -f _CoqProject -o Makefile
  make .merlin
  make
  make install
)
