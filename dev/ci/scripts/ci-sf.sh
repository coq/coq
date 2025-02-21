#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download sf

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

cd "$CI_BUILD_DIR/sf"

( cd lf-current
  make
)

( cd plf-current
  make
)

( cd vfa-current
  make
)

( cd slf-current
  make
)

# ( cd qc-current
#   make clean
#   make
# )
