#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download equations

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/equations"
  [ -e Makefile.rocq ] || ./configure.sh
  make -f Makefile.rocq .merlin
  make
  make install
)
