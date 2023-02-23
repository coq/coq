#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download compcert

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQCOPTS='-native-compiler no -w -undeclared-scope -w -omega-is-deprecated'
( cd "${CI_BUILD_DIR}/compcert"
  [ -e Makefile.config ] || ./configure -ignore-coq-version x86_32-linux -use-external-MenhirLib -use-external-Flocq
  make
  make check-proof COQCHK='"$(COQBIN)coqchk" -silent -o $(COQINCLUDES)'
)
