#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

bedrock2_CI_DIR="${CI_BUILD_DIR}/bedrock2"

git_checkout "${bedrock2_CI_BRANCH}" "${bedrock2_CI_GITURL}" "${bedrock2_CI_DIR}"
( cd "${bedrock2_CI_DIR}" && git submodule update --init --recursive )

( cd "${bedrock2_CI_DIR}" && make )
