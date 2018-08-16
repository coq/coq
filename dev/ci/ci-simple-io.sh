#!/usr/bin/env bash

ci_dir="$(dirname "$0")"

. "${ci_dir}/ci-common.sh"

simple_io_CI_DIR="${CI_BUILD_DIR}/simple-io"

git_checkout "${simple_io_CI_BRANCH}" "${simple_io_CI_GITURL}" "${simple_io_CI_DIR}"

( cd "${simple_io_CI_DIR}" && make build && make install)
