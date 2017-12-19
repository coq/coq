#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

Equations_CI_DIR=${CI_BUILD_DIR}/Equations

git_checkout ${Equations_CI_BRANCH} ${Equations_CI_GITURL} ${Equations_CI_DIR}

( cd ${Equations_CI_DIR} && coq_makefile -f _CoqProject -o Makefile && make && make test-suite && make examples && make install)
