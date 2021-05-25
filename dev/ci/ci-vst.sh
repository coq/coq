#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download vst

export COMPCERT=bundled

sed -i.bak 's/\(COQC=.*\)/\1 -native-compiler no/' "$CI_BUILD_DIR/vst/Makefile"
( cd "${CI_BUILD_DIR}/vst"
  make IGNORECOQVERSION=true
)
