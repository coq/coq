#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download unimath

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/unimath"
  # these files consumes too much memory for the shared workers
  # (at least with -j 2 when the scheduler runs them in parallel)
  for p in SubstitutionSystems Bicategories ModelCategories; do
      sed -i.bak "s|PACKAGES += $p||" Makefile
  done
  make BUILD_COQ=no
)
