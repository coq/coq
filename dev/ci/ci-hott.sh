#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download HoTT

( cd "${CI_BUILD_DIR}/HoTT" && ./autogen.sh && ./configure && make && make validate )
