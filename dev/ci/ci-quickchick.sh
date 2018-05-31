#!/usr/bin/env bash

ci_dir="$(dirname "$0")"

# This script could be included inside other ones
# Let's avoid to source ci-common twice in this case
if [ -z "${CI_BUILD_DIR}" ];
then
    . "${ci_dir}/ci-common.sh"
fi

quickchick_CI_DIR="${CI_BUILD_DIR}/Quickchick"

install_ssreflect

git_checkout "${quickchick_CI_BRANCH}" "${quickchick_CI_GITURL}" "${quickchick_CI_DIR}"

( cd "${quickchick_CI_DIR}" && make && make install)
