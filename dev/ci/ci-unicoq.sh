#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download unicoq

( cd "${CI_BUILD_DIR}/unicoq" && coq_makefile -f Make -o Makefile && make && make install )
