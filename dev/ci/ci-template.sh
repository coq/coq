#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

Template_CI_BRANCH=master
Template_CI_GITURL=https://github.com/Template/Template
Template_CI_DIR="${CI_BUILD_DIR}/Template"

git_checkout "${Template_CI_BRANCH}" "${Template_CI_GITURL}" "${Template_CI_DIR}"

( cd "${Template_CI_DIR}" && make )
