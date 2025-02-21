#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

WITH_SUBMODULES=1
git_download rupicola

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

make_args=(EXTERNAL_COQUTIL=1 EXTERNAL_BEDROCK2=1)

export COQEXTRAFLAGS='-native-compiler no' # following bedrock2
( cd "${CI_BUILD_DIR}/rupicola"
  make "${make_args[@]}"
  make "${make_args[@]}" install
)
