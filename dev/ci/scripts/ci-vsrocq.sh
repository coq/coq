#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download vsrocq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

if [ -n "${GITLAB_CI}" ]; then
  export ROCQLIB="$PWD/_install_ci/lib/coq"
  export ROCQRUNTIMELIB="$PWD/_install_ci/lib/rocq-runtime"
fi

( cd "$CI_BUILD_DIR/vsrocq/language-server"
  make dune-files
  dune build --root . --only-packages=vsrocq-language-server @install
  # dune runtest --root .
  dune install --root . vsrocq-language-server --prefix="$CI_INSTALL_DIR"
)
