#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download fiat_crypto

# We need a larger stack size to not overflow ocamlopt+flambda when
# building the executables.
# c.f. https://github.com/coq/coq/pull/8313#issuecomment-416650241

( cd "${CI_BUILD_DIR}/fiat_crypto" && git submodule update --init --recursive && \
  ulimit -s 32768 && make new-pipeline c-files )
