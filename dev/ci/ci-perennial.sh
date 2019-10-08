#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download perennial

# required by Perennial's coqc.py build wrapper
export LC_ALL=C.UTF-8

( cd "${CI_BUILD_DIR}/perennial" && git submodule update --init --recursive && make TIMED=false )
