#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download mathcomp_word

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/mathcomp_word"
  dune build @install -p coq-mathcomp-word
  dune install -p coq-mathcomp-word --prefix="$CI_INSTALL_DIR"
)
