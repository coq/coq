#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download vst

export COMPCERT=bundled

( cd "${CI_BUILD_DIR}/vst" && make IGNORECOQVERSION=true )
