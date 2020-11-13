#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download perennial

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/perennial" && git submodule update --init --recursive && make TIMED=false lite )
