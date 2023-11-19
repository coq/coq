#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download corn

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

COQEXTRAFLAGS="$COQEXTRAFLAGS -native-compiler no"
( cd "${CI_BUILD_DIR}/corn"
  ./configure.sh
  make
  make install
)
