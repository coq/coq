#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

cross_crypto_CI_DIR="${CI_BUILD_DIR}/cross-crypto"

git_checkout "${cross_crypto_CI_BRANCH}" "${cross_crypto_CI_GITURL}" "${cross_crypto_CI_DIR}"
( cd "${cross_crypto_CI_DIR}" && git submodule update --init --recursive )

( cd "${cross_crypto_CI_DIR}" && make )
