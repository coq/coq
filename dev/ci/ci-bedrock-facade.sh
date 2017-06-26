#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

bedrock_facade_CI_DIR=${CI_BUILD_DIR}/bedrock-facade

git_checkout ${bedrock_facade_CI_BRANCH} ${bedrock_facade_CI_GITURL} ${bedrock_facade_CI_DIR}
( cd ${bedrock_facade_CI_DIR} && git submodule update --init --recursive )

( cd ${bedrock_facade_CI_DIR} && (make facade TIMED=1 2>&1 | tee time-of-build.log; exit ${PIPESTATUS[0]}) && python ./etc/coq-scripts/timing/make-one-time-file.py time-of-build.log time-of-build-pretty.log && cat time-of-build-pretty.log )
