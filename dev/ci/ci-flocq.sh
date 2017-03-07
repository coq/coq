#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

Flocq_CI_BRANCH=master
Flocq_CI_GITURL=https://scm.gforge.inria.fr/anonscm/git/flocq/flocq.git
Flocq_CI_DIR=${CI_BUILD_DIR}/flocq

git_checkout ${Flocq_CI_BRANCH} ${Flocq_CI_GITURL} ${Flocq_CI_DIR}

( cd ${Flocq_CI_DIR} && ./autogen.sh && ./configure && ./remake -j${NJOBS} )
