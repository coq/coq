#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

CoLoR_CI_DIR=${CI_BUILD_DIR}/color

# Setup Bignums
source ${ci_dir}/ci-bignums.sh

# Compile CoLoR
git_checkout ${CoLoR_CI_BRANCH} ${CoLoR_CI_GITURL} ${CoLoR_CI_DIR}
( cd ${CoLoR_CI_DIR} && make )
