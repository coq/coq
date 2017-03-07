#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

install_ssreflect

# Setup stdpp
git_checkout master https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp.git coq-stdpp

( cd coq-stdpp && make -j ${NJOBS} && make install )

# Setup Iris
git_checkout master https://gitlab.mpi-sws.org/FP/iris-coq.git iris-coq

( cd iris-coq && make -j ${NJOBS} )
