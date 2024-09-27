#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

make_args=(EXTERNAL_COQUTIL=1 EXTERNAL_RISCV_COQ=1 EXTERNAL_KAMI=1)

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/bedrock2"
  COQMF_ARGS='-arg "-async-proofs-tac-j 1"' make "${make_args[@]}"
  make "${make_args[@]}"
)
