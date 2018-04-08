#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

Coquelicot_CI_DIR="${CI_BUILD_DIR}/coquelicot"

install_ssreflect

git_checkout "${Coquelicot_CI_BRANCH}" "${Coquelicot_CI_GITURL}" "${Coquelicot_CI_DIR}"

( cd "${Coquelicot_CI_DIR}" && ./autogen.sh && ./configure && ./remake "-j${NJOBS}" )
