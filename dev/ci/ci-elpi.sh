#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

Elpi_CI_DIR="${CI_BUILD_DIR}/elpi"

git_checkout "${Elpi_CI_BRANCH}" "${Elpi_CI_GITURL}" "${Elpi_CI_DIR}"

( cd "${Elpi_CI_DIR}" && make && make install )
