#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download elpi

( cd "${CI_BUILD_DIR}/elpi" && make && make install )

git_download elpi_hb

( cd "${CI_BUILD_DIR}/elpi_hb" && make && make install )
