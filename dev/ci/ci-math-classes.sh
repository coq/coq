#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

math_classes_CI_DIR="${CI_BUILD_DIR}/math-classes"

git_checkout "${math_classes_CI_BRANCH}" "${math_classes_CI_GITURL}" "${math_classes_CI_DIR}"

( cd "${math_classes_CI_DIR}" && ./configure.sh && make && make install )
