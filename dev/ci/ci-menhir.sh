#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download menhirlib

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/menhirlib"
  if grep -q unreleased dune-project; then
    date=$(date +%Y%m%d)
    sed -i.bak "s/unreleased/$date/" dune-project
    echo "Definition require_$date := tt." > coq-menhirlib/src/Version.v
  fi

  make -C coq-menhirlib
  make -C coq-menhirlib install
)
