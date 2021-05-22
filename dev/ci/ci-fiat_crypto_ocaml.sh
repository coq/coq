#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

make_args=(EXTERNAL_REWRITER=1 EXTERNAL_COQPRIME=1)

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/fiat_crypto"
  make "${make_args[@]}" standalone-ocaml lite-generated-files
)
