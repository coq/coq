#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download relation_algebra

( cd "${CI_BUILD_DIR}/relation_algebra" && make && make install )
