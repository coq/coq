#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

stdpp_CI_DIR=${CI_BUILD_DIR}/coq-stdpp

Iris_CI_DIR=${CI_BUILD_DIR}/iris-coq

install_ssreflect

# Setup Iris first, as it is needed to compute the dependencies

git_checkout ${Iris_CI_BRANCH} ${Iris_CI_GITURL} ${Iris_CI_DIR}
read -a IRIS_DEP < ${Iris_CI_DIR}/opam.pins

# Setup stdpp
stdpp_CI_GITURL=${IRIS_DEP[1]}.git
stdpp_CI_COMMIT=${IRIS_DEP[2]}

git_checkout ${stdpp_CI_BRANCH} ${stdpp_CI_GITURL} ${stdpp_CI_DIR} ${stdpp_CI_COMMIT}

( cd ${stdpp_CI_DIR} && make pretty-timed TGTS="all" && make install )

# Build iris now
( cd ${Iris_CI_DIR} && make pretty-timed TGTS="all" )
