#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download UniMath

( cd "${CI_BUILD_DIR}/UniMath" && make BUILD_COQ=no )
