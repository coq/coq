#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download rewriter

( cd "${CI_BUILD_DIR}/rewriter" && make && make install )
