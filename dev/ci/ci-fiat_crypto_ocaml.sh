#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

fiat_crypto_CI_MAKE_ARGS="EXTERNAL_REWRITER=1 EXTERNAL_COQPRIME=1"

( cd "${CI_BUILD_DIR}/fiat_crypto" && make ${fiat_crypto_CI_MAKE_ARGS} standalone-ocaml lite-generated-files )
