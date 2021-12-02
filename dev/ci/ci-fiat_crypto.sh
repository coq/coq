#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

WITH_SUBMODULES=1
git_download fiat_crypto

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

# We need a larger stack size to not overflow ocamlopt+flambda when
# building the executables.
# c.f. https://github.com/coq/coq/pull/8313#issuecomment-416650241
# c.f. https://coq.zulipchat.com/#narrow/stream/237656-Coq-devs.20.26.20plugin.20devs/topic/fiat.20crypto.20broken/near/263463085
stacksize=65536

# fiat-crypto is not guaranteed to build with the latest version of
# bedrock2, so we use the pinned version of bedrock2, but the external
# version of other developments
make_args=(EXTERNAL_REWRITER=1 EXTERNAL_COQPRIME=1)

( cd "${CI_BUILD_DIR}/fiat_crypto"
  ulimit -s $stacksize
  make "${make_args[@]}" pre-standalone-extracted printlite lite
  make -j 1 "${make_args[@]}" all-except-compiled
)
