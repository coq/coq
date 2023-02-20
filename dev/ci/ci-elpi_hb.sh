#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download elpi
git_download hierarchy_builder

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/elpi"
  make build-core
  make build-apps
  make install
)

( cd "${CI_BUILD_DIR}/hierarchy_builder"
  make config
  make build
  make install
)
