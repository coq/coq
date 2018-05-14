#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

mathcomp_CI_DIR="${CI_BUILD_DIR}/math-comp"
oddorder_CI_DIR="${CI_BUILD_DIR}/odd-order"

git_checkout "${mathcomp_CI_BRANCH}" "${mathcomp_CI_GITURL}" "${mathcomp_CI_DIR}"
git_checkout "${oddorder_CI_BRANCH}" "${oddorder_CI_GITURL}" "${oddorder_CI_DIR}"

( cd "${mathcomp_CI_DIR}/mathcomp" && make && make install )
( cd "${oddorder_CI_DIR}/" && make )
