#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

bedrock_src_CI_DIR=${CI_BUILD_DIR}/bedrock-src

git_checkout ${bedrock_src_CI_BRANCH} ${bedrock_src_CI_GITURL} ${bedrock_src_CI_DIR}

( cd ${bedrock_src_CI_DIR} && ./etc/coq-scripts/timing/make-pretty-timed-or-error.sh -j ${NJOBS} src )
