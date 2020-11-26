#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download mathcomp

( cd "${CI_BUILD_DIR}/mathcomp/mathcomp" && make && make test-suite && make install )
