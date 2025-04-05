#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download metarocq

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/metarocq"
  [ -e pcuic/metarocq-config ] || ./configure.sh local
  make all TIMED=pretty-timed
  make test-suite TIMED=pretty-timed
  make install
)
