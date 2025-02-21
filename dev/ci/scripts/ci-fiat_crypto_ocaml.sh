#!/usr/bin/env bash

set -e

# fiat-crypto job sets up the sources
if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

# We set the stack size to 128MiB to be able to build with flambda
# See https://github.com/ocaml/ocaml/issues/7842
ulimit -s 131072

# Regardless of where the dependencies came from when building
# ci-fiat_crypto, we don't need them for building the OCaml
# binaries and lite C files, so we use all external dependencies.
# we explicitly pass OCAMLFIND so that we pick up the opam
# (non-flambda one) rather than the one used to build coq
make_args=(EXTERNAL_DEPENDENCIES=1 OCAMLFIND=ocamlfind)

( cd "${CI_BUILD_DIR}/fiat_crypto"
  make "${make_args[@]}" -j 1 lite-c-files
)
