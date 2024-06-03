#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download serapi

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/serapi"
  make
  make test
  # Not needed by any other CI job for now, but we still install just
  # in case
  dune install -p coq-serapi --prefix="$CI_INSTALL_DIR"
)
