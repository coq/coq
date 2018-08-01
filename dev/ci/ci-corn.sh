#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

Corn_CI_DIR="${CI_BUILD_DIR}/corn"

git_checkout "${Corn_CI_BRANCH}" "${Corn_CI_GITURL}" "${Corn_CI_DIR}"

( cd "${Corn_CI_DIR}" && make && make install )
