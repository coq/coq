#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

install_ssreflect

git_download fcsl_pcm

( cd "${CI_BUILD_DIR}/fcsl_pcm" && make )
