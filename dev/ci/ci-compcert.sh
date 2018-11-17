#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download compcert

( cd "${CI_BUILD_DIR}/compcert" && \
  ./configure -ignore-coq-version x86_32-linux && make && make check-proof )
