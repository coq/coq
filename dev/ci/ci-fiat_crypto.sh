#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download fiat_crypto

# We need a larger stack size to not overflow ocamlopt+flambda when
# building the executables.
# c.f. https://github.com/coq/coq/pull/8313#issuecomment-416650241
fiat_crypto_CI_STACKSIZE=32768

# fiat-crypto is not guaranteed to build with the latest version of
# bedrock2, so we use the pinned version of bedrock2, but the external
# version of other developments
fiat_crypto_CI_MAKE_ARGS="EXTERNAL_REWRITER=1 EXTERNAL_COQPRIME=1"
fiat_crypto_CI_TARGETS1="${fiat_crypto_CI_MAKE_ARGS} pre-standalone-extracted printlite lite"
fiat_crypto_CI_TARGETS2="${fiat_crypto_CI_MAKE_ARGS} all-except-compiled"

( cd "${CI_BUILD_DIR}/fiat_crypto" && git submodule update --init --recursive && \
        ulimit -s ${fiat_crypto_CI_STACKSIZE} && \
        make ${fiat_crypto_CI_TARGETS1} && make -j 1 ${fiat_crypto_CI_TARGETS2} )
