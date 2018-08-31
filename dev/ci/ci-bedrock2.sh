#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download bedrock2

( cd "${CI_BUILD_DIR}/bedrock2" && git submodule update --init --recursive && make )
