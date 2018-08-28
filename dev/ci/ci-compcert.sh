#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download CompCert

( cd "${CI_BUILD_DIR}/CompCert" && \
  ./configure -ignore-coq-version x86_32-linux && make && make check-proof )
