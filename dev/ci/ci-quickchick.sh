#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

install_ssreflect

git_download quickchick

( cd "${CI_BUILD_DIR}/quickchick" && make && make install)
