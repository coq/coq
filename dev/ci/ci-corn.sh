#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download Corn

( cd "${CI_BUILD_DIR}/Corn" && make && make install )
