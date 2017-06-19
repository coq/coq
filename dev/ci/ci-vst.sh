#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

VST_CI_DIR=${CI_BUILD_DIR}/VST

# opam install -j ${NJOBS} -y menhir
git_checkout ${VST_CI_BRANCH} ${VST_CI_GITURL} ${VST_CI_DIR}

# Targets are: msl veric floyd
# Patch to avoid the upper version limit
( cd ${VST_CI_DIR} && sed -i.bak 's/8.6$/8.6 or-else trunk/' Makefile && make )
