#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

stdpp_CI_BRANCH=master
stdpp_CI_GITURL=https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp.git
stdpp_CI_DIR=${CI_BUILD_DIR}/coq-stdpp

Iris_CI_BRANCH=master
Iris_CI_GITURL=https://gitlab.mpi-sws.org/FP/iris-coq.git
Iris_CI_DIR=${CI_BUILD_DIR}/iris-coq

install_ssreflect

# Setup stdpp

git_checkout ${stdpp_CI_BRANCH} ${stdpp_CI_GITURL} ${stdpp_CI_DIR}

( cd ${stdpp_CI_DIR} && make -j ${NJOBS} && make install )

# Setup Iris

git_checkout ${Iris_CI_BRANCH} ${Iris_CI_GITURL} ${Iris_CI_DIR}

( cd ${Iris_CI_DIR} && make -j ${NJOBS} )
