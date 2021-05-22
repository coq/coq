#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coq_dpdgraph

( cd "${CI_BUILD_DIR}/coq_dpdgraph"
  autoconf
  ./configure
  make
  make test-suite
)
