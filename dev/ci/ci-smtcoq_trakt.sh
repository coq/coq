#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download smtcoq_trakt

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/smtcoq_trakt"
  make -C src .merlin
  make
  make install
)
