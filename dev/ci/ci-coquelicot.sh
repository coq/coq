#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coquelicot

( cd "${CI_BUILD_DIR}/coquelicot" && ( if [ ! -x ./configure ]; then autoreconf -i -s && ./configure; fi ) && ./remake "-j${NJOBS}" && ./remake install )
