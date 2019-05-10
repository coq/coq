#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

install_ssreflect

git_download coquelicot

( cd "${CI_BUILD_DIR}/coquelicot" && ./autogen.sh && ./configure && ./remake "-j${NJOBS}" )
