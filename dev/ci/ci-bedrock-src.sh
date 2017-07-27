#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

bedrock_src_CI_DIR=${CI_BUILD_DIR}/bedrock-src

git_checkout ${bedrock_src_CI_BRANCH} ${bedrock_src_CI_GITURL} ${bedrock_src_CI_DIR}
( cd ${bedrock_src_CI_DIR} && git submodule update --init --recursive )

( cd ${bedrock_src_CI_DIR} && (make src TIMED=1 2>&1 | tee time-of-build.log; exit ${PIPESTATUS[0]}) && python ./etc/coq-scripts/timing/make-one-time-file.py time-of-build.log time-of-build-pretty.log && cat time-of-build-pretty.log )
