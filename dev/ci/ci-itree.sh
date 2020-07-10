#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download itree

( cd "${CI_BUILD_DIR}/itree" && make && make install )
