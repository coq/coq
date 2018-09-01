#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download tlc

( cd "${CI_BUILD_DIR}/tlc" && make )
