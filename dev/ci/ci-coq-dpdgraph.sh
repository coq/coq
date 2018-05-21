#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

coq_dpdgraph_CI_DIR="${CI_BUILD_DIR}/coq-dpdgraph"

git_checkout "${coq_dpdgraph_CI_BRANCH}" "${coq_dpdgraph_CI_GITURL}" "${coq_dpdgraph_CI_DIR}"

( cd "${coq_dpdgraph_CI_DIR}" && autoconf && ./configure && make && make test-suite )
