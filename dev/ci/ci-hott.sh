#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

HoTT_CI_DIR=${CI_BUILD_DIR}/HoTT

git_checkout ${HoTT_CI_BRANCH} ${HoTT_CI_GITURL} ${HoTT_CI_DIR}
( cd ${HoTT_CI_DIR} && git submodule update --init --recursive )

( cd ${HoTT_CI_DIR} && ./autogen.sh && ./configure && (make TIMED=1 2>&1 | tee time-of-build.log; exit ${PIPESTATUS[0]}) && python ./etc/coq-scripts/timing/make-one-time-file.py time-of-build.log time-of-build-pretty.log && cat time-of-build-pretty.log )
