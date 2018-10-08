#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download aactactics

( cd "${CI_BUILD_DIR}/aactactics" && make && make install )
