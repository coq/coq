#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download Flocq

( cd "${CI_BUILD_DIR}/Flocq" && autoconf && ./configure && ./remake "-j${NJOBS}" )
