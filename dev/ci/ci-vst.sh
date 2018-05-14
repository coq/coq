#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

VST_CI_DIR="${CI_BUILD_DIR}/VST"

git_checkout "${VST_CI_BRANCH}" "${VST_CI_GITURL}" "${VST_CI_DIR}"

( cd "${VST_CI_DIR}" && make IGNORECOQVERSION=true )
