#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download flocq

( cd "${CI_BUILD_DIR}/flocq" && autoconf && ./configure && ./remake "-j${NJOBS}" && ./remake install )
