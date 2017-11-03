#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

paramcoq_CI_DIR=${CI_BUILD_DIR}/paramcoq

git_checkout ${paramcoq_CI_BRANCH} ${paramcoq_CI_GITURL} ${paramcoq_CI_DIR}

( cd ${paramcoq_CI_DIR} && make -j ${NJOBS} )
