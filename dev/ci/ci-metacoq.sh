#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download metacoq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/metacoq"
  [ -e pcuic/metacoq-config ] || ./configure.sh local
  make all TIMED=pretty-timed
  make test-suite TIMED=pretty-timed
  make install
)
