#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

mathcomp_CI_DIR="${CI_BUILD_DIR}/math-comp"

git_checkout "${mathcomp_CI_BRANCH}" "${mathcomp_CI_GITURL}" "${mathcomp_CI_DIR}"

( cd "${mathcomp_CI_DIR}/mathcomp" && make )
