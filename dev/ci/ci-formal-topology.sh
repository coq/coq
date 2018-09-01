#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download formal_topology

( cd "${CI_BUILD_DIR}/formal_topology" && make )
