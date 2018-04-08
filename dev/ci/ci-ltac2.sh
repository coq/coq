#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

ltac2_CI_DIR="${CI_BUILD_DIR}/ltac2"

git_checkout "${ltac2_CI_BRANCH}" "${ltac2_CI_GITURL}" "${ltac2_CI_DIR}"

( cd "${ltac2_CI_DIR}" && make && make tests && make install )
