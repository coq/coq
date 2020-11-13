#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download color

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/color" && make )
