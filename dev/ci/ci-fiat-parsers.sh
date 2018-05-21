#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

fiat_parsers_CI_DIR="${CI_BUILD_DIR}/fiat"

git_checkout "${fiat_parsers_CI_BRANCH}" "${fiat_parsers_CI_GITURL}" "${fiat_parsers_CI_DIR}"

( cd "${fiat_parsers_CI_DIR}" && make parsers parsers-examples && make fiat-core )
