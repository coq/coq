#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download metacoq

( cd "${CI_BUILD_DIR}/metacoq" && ./configure.sh local && make ci-local && make install )
