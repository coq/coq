#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download paramcoq

( cd "${CI_BUILD_DIR}/paramcoq" && make && make install )
