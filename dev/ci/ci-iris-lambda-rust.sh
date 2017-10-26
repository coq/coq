#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

stdpp_CI_DIR=${CI_BUILD_DIR}/coq-stdpp
Iris_CI_DIR=${CI_BUILD_DIR}/iris-coq
lambdaRust_CI_DIR=${CI_BUILD_DIR}/lambdaRust

install_ssreflect

# Add or update the opam repo we need for dependency resolution
opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git -p 0 || opam update iris-dev

# Setup lambdaRust first
git_checkout ${lambdaRust_CI_BRANCH} ${lambdaRust_CI_GITURL} ${lambdaRust_CI_DIR}

# Extract required version of Iris
Iris_VERSION=$(cat ${lambdaRust_CI_DIR}/opam | fgrep coq-iris | egrep 'dev\.([0-9.-]+)' -o)
Iris_URL=$(opam show coq-iris.$Iris_VERSION -f upstream-url)
read -a Iris_URL_PARTS <<< $(echo $Iris_URL | tr '#' ' ')

# Setup Iris
git_checkout ${Iris_CI_BRANCH} ${Iris_URL_PARTS[0]} ${Iris_CI_DIR} ${Iris_URL_PARTS[1]}

# Extract required version of std++
stdpp_VERSION=$(cat ${Iris_CI_DIR}/opam | fgrep coq-stdpp | egrep 'dev\.([0-9.-]+)' -o)
stdpp_URL=$(opam show coq-stdpp.$stdpp_VERSION -f upstream-url)
read -a stdpp_URL_PARTS <<< $(echo $stdpp_URL | tr '#' ' ')

# Setup std++
git_checkout ${stdpp_CI_BRANCH} ${stdpp_URL_PARTS[0]} ${stdpp_CI_DIR} ${stdpp_URL_PARTS[1]}

# Build std++
( cd ${stdpp_CI_DIR} && make && make install )

# Build iris
( cd ${Iris_CI_DIR} && make && make install )

# Build lambdaRust
( cd ${lambdaRust_CI_DIR} && make && make install )
