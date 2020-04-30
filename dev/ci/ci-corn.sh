#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download corn

( cd "${CI_BUILD_DIR}/corn" && ./configure.sh && make && make install )
