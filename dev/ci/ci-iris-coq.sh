#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

stdpp_CI_DIR=${CI_BUILD_DIR}/coq-stdpp

Iris_CI_DIR=${CI_BUILD_DIR}/iris-coq

install_ssreflect

# Add or update the opam repo we need for dependency resolution
opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git -p 0 || opam update iris-dev

# Setup Iris first, extract required version of std++
git_checkout ${Iris_CI_BRANCH} ${Iris_CI_GITURL} ${Iris_CI_DIR}
stdpp_VERSION=$(cat ${Iris_CI_DIR}/opam | fgrep coq-stdpp | egrep 'dev\.([0-9.-]+)' -o)

# Ask opam where to get this std++, separating at the #
stdpp_URL=$(opam show coq-stdpp.$stdpp_VERSION -f upstream-url)
read -a stdpp_URL_PARTS <<< $(echo $stdpp_URL | tr '#' ' ')

# Setup std++
git_checkout ${stdpp_CI_BRANCH} ${stdpp_URL_PARTS[0]} ${stdpp_CI_DIR} ${stdpp_URL_PARTS[1]}
( cd ${stdpp_CI_DIR} && make && make install )

# Build iris now
( cd ${Iris_CI_DIR} && make )
