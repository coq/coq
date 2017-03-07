#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

UniMath_CI_BRANCH=master
UniMath_CI_GITURL=https://github.com/UniMath/UniMath.git
UniMath_CI_DIR=${CI_BUILD_DIR}/UniMath

git_checkout ${UniMath_CI_BRANCH} ${UniMath_CI_GITURL} ${UniMath_CI_DIR}

( cd ${UniMath_CI_DIR}                        && \
  sed -i.bak '/Folds/d'              Makefile && \
  sed -i.bak '/HomologicalAlgebra/d' Makefile && \
  make -j ${NJOBS} BUILD_COQ=no )

