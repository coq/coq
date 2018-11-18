#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download equations

( cd "${CI_BUILD_DIR}/equations" && coq_makefile -f _CoqProject -o Makefile && \
  make && make test-suite && make examples && make install)
