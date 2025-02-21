#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

WITH_SUBMODULES=1
git_download bedrock2

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

make_args=(EXTERNAL_COQUTIL=1 EXTERNAL_RISCV_COQ=1 EXTERNAL_KAMI=1)

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/bedrock2"
  COQMF_ARGS='-arg "-async-proofs-tac-j 1"' make "${make_args[@]}" bedrock2_ex compiler_noex
  make "${make_args[@]}" install_bedrock2_ex install_compiler
)
