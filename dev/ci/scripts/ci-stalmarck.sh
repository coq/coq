#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download stalmarck

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/stalmarck"
  make
  make install

  rm -f coq-stalmarck.opam # work around https://github.com/ocaml/dune/issues/4814
  dune build @install -p coq-stalmarck-tactic
  dune install -p coq-stalmarck-tactic --prefix="$CI_INSTALL_DIR"
)
