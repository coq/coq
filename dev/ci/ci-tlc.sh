#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

tlc_CI_DIR="${CI_BUILD_DIR}/tlc"

git_checkout "${tlc_CI_BRANCH}" "${tlc_CI_GITURL}" "${tlc_CI_DIR}"

( cd "${tlc_CI_DIR}" && make )
