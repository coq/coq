#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download vscoq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "$CI_BUILD_DIR/vscoq/language-server"
  dune build --root . --only-packages=vscoq-language-server @install
  dune runtest --root .
)
