#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download paco

( cd "${CI_BUILD_DIR}/paco/src" && make && make -f Makefile.coq install )
