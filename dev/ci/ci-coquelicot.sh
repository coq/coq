#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

install_ssreflect

FORCE_GIT=1
git_download Coquelicot

( cd "${CI_BUILD_DIR}/Coquelicot" && ./autogen.sh && ./configure && ./remake "-j${NJOBS}" )
