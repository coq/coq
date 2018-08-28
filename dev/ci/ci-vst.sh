#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download VST

( cd "${CI_BUILD_DIR}/VST" && make IGNORECOQVERSION=true )
