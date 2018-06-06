#!/usr/bin/env bash

ci_dir="$(dirname "$0")"

# This script could be included inside other ones
# Let's avoid to source ci-common twice in this case
if [ -z "${CI_BUILD_DIR}" ];
then
    . "${ci_dir}/ci-common.sh"
fi

ext_lib_CI_DIR="${CI_BUILD_DIR}/ExtLib"

git_checkout "${ext_lib_CI_BRANCH}" "${ext_lib_CI_GITURL}" "${ext_lib_CI_DIR}"

( cd "${ext_lib_CI_DIR}" && make && make install)
