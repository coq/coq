#!/usr/bin/env bash

set -e

# fiat-crypto job sets up the sources
if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

make_args=(EXTERNAL_REWRITER=1 EXTERNAL_COQPRIME=1)

( cd "${CI_BUILD_DIR}/fiat_crypto"
  make "${make_args[@]}" standalone-ocaml lite-generated-files
)
