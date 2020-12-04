#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download tactician

( cd "${CI_BUILD_DIR}/coq-tactician" && dune build )
