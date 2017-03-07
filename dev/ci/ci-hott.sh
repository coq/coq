#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

HoTT_CI_BRANCH=mz-8.7
HoTT_CI_GITURL=https://github.com/ejgallego/HoTT.git
HoTT_CI_DIR=${CI_BUILD_DIR}/HoTT

git_checkout ${HoTT_CI_BRANCH} ${HoTT_CI_GITURL} ${HoTT_CI_DIR}

( cd ${HoTT_CI_DIR} && ./autogen.sh && ./configure && make -j ${NJOBS} )
