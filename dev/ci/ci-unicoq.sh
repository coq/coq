#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

unicoq_CI_DIR=${CI_BUILD_DIR}/unicoq

git_checkout ${unicoq_CI_BRANCH} ${unicoq_CI_GITURL} ${unicoq_CI_DIR}

( cd ${unicoq_CI_DIR} && coq_makefile -f Make -o makefile && make -j ${NJOBS} && make install )

