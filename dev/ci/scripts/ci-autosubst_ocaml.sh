#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download autosubst_ocaml

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/autosubst_ocaml"
  dune build @install -p coq-autosubst-ocaml
  dune install -p coq-autosubst-ocaml --prefix="$CI_INSTALL_DIR"
)
