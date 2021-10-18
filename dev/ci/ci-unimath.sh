#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download unimath

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/unimath"
  # DisplayedInserter consumes too much memory for the shared workers
  sed -i.bak 's|DisplayedBicats/Examples/DisplayedInserter.v||'  UniMath/Bicategories/.package/files
  make BUILD_COQ=no
)
