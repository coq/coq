#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download equations

( cd "${CI_BUILD_DIR}/equations" && ./configure.sh coq && make ci && make install )
