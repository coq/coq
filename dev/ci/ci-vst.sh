#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download vst

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

# sometimes (rarely) CompCert master can break VST and it can take
# weeks or months for VST to catch up, in this case, just uncomment
# the line below to use the compcert version bundled in VST
# export COMPCERT=bundled

# See ci-compcert.sh
export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/vst"
  make IGNORECOQVERSION=true IGNORECOMPCERTVERSION=true
)
