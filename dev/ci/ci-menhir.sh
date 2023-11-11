#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download menhirlib

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/menhirlib"
  sed -i.bak "s/unreleased/$(date +%Y%m%d)/" dune-project
  echo "Definition require_$(date +%Y%m%d) := tt." > coq-menhirlib/src/Version.v
  dune build @install -p menhirLib,menhirSdk,menhir
  dune install -p menhirLib,menhirSdk,menhir menhir menhirSdk menhirLib --prefix="$CI_INSTALL_DIR"

  make -C coq-menhirlib
  make -C coq-menhirlib install
)
