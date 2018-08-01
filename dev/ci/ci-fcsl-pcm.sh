#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

fcsl_pcm_CI_DIR="${CI_BUILD_DIR}/fcsl-pcm"

install_ssreflect

git_checkout "${fcsl_pcm_CI_BRANCH}" "${fcsl_pcm_CI_GITURL}" "${fcsl_pcm_CI_DIR}"

( cd "${fcsl_pcm_CI_DIR}" && make )
