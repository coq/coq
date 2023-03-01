#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coq_dpdgraph

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/coq_dpdgraph"
  dune build @install -p coq-dpdgraph
  dune install -p coq-dpdgraph --prefix="$CI_INSTALL_DIR"
)
