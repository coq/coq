#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

# We need a larger stack size to not overflow ocamlopt+flambda when
# building the executables.
# c.f. https://github.com/coq/coq/pull/8313#issuecomment-416650241
stacksize=32768

# fiat-crypto is not guaranteed to build with the latest version of
# bedrock2, so we use the pinned version of bedrock2, but the external
# version of other developments
make_args=(EXTERNAL_REWRITER=1 EXTERNAL_COQPRIME=1)

export COQEXTRAFLAGS='-native-compiler no' # following bedrock2

( cd "${CI_BUILD_DIR}/fiat_crypto"
  ulimit -s $stacksize
  if ! grep -q async-proofs-tac-j Makefile.coq.local; then
    echo 'OTHERFLAGS += -async-proofs-tac-j 0' > tmp
    cat Makefile.coq.local >> tmp
    mv tmp Makefile.coq.local
  fi
  make "${make_args[@]}" pre-standalone-extracted printlite lite ||
    make -j 1 "${make_args[@]}" pre-standalone-extracted printlite lite
  make "${make_args[@]}" all-except-compiled ||
    make -j 1 "${make_args[@]}" all-except-compiled
)
