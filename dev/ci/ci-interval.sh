#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download interval

( cd "${CI_BUILD_DIR}/interval" && autoconf && ./configure && ./remake "-j${NJOBS}" && ./remake install )
