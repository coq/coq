#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

WITH_SUBMODULES=1
git_download bedrock2

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/bedrock2"
  COQMF_ARGS='-arg "-async-proofs-tac-j 1"' make
  make install
)
