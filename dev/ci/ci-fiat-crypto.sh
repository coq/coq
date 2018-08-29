#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

fiat_crypto_CI_DIR="${CI_BUILD_DIR}/fiat-crypto"

git_checkout "${fiat_crypto_CI_BRANCH}" "${fiat_crypto_CI_GITURL}" "${fiat_crypto_CI_DIR}"
( cd "${fiat_crypto_CI_DIR}" && git submodule update --init --recursive )

# We need a larger stack size to not overflow ocamlopt+flambda when
# building the executables.
# c.f. https://github.com/coq/coq/pull/8313#issuecomment-416650241
( cd "${fiat_crypto_CI_DIR}" && ulimit -s 32768 && make new-pipeline c-files )
