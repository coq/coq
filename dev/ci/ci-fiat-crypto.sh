#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

fiat_crypto_CI_DIR=${CI_BUILD_DIR}/fiat-crypto

git_checkout ${fiat_crypto_CI_BRANCH} ${fiat_crypto_CI_GITURL} ${fiat_crypto_CI_DIR}

( cd ${fiat_crypto_CI_DIR} && make -j ${NJOBS} lite )
