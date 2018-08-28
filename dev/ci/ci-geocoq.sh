#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

install_ssralg

git_download GeoCoq

( cd "${CI_BUILD_DIR}/GeoCoq" && ./configure.sh && make )
