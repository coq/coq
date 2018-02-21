#!/usr/bin/env bash

ci_dir="$(dirname "$0")"

# This script could be included inside other ones
# Let's avoid to source ci-common twice in this case
if [ -z "${CI_BUILD_DIR}" ];
then
    . "${ci_dir}/ci-common.sh"
fi

bignums_CI_DIR="${CI_BUILD_DIR}/Bignums"

git_checkout "${bignums_CI_BRANCH}" "${bignums_CI_GITURL}" "${bignums_CI_DIR}"

( cd "${bignums_CI_DIR}" && make && make install)
