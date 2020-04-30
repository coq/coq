#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download math_classes

( cd "${CI_BUILD_DIR}/math_classes" && ./configure.sh && make && make install )
