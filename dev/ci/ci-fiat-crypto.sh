#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

fiat_crypto_CI_DIR=${CI_BUILD_DIR}/fiat-crypto

git_checkout ${fiat_crypto_CI_BRANCH} ${fiat_crypto_CI_GITURL} ${fiat_crypto_CI_DIR}
( cd ${fiat_crypto_CI_DIR} && git submodule update --init --recursive )

( cd ${fiat_crypto_CI_DIR} && (make lite TIMED=1 2>&1 | tee time-of-build.log; exit ${PIPESTATUS[0]}) && python ./etc/coq-scripts/timing/make-one-time-file.py time-of-build.log time-of-build-pretty.log && cat time-of-build-pretty.log )
