#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

GeoCoq_CI_DIR="${CI_BUILD_DIR}/GeoCoq"

git_checkout "${GeoCoq_CI_BRANCH}" "${GeoCoq_CI_GITURL}" "${GeoCoq_CI_DIR}"

( cd "${GeoCoq_CI_DIR}"                                     && \
  ./configure-ci.sh                                       && \
  make )
