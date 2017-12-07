#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

Color_CI_DIR=${CI_BUILD_DIR}/color

# Setup Bignums

source ${ci_dir}/ci-bignums.sh

# Compiles CoLoR

svn checkout ${Color_CI_SVNURL} ${Color_CI_DIR}

( cd ${Color_CI_DIR} && make )
