#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

math_classes_CI_DIR=${CI_BUILD_DIR}/math-classes

Corn_CI_DIR=${CI_BUILD_DIR}/corn

formal_topology_CI_DIR=${CI_BUILD_DIR}/formal-topology

# Setup Math-Classes

git_checkout ${math_classes_CI_BRANCH} ${math_classes_CI_GITURL} ${math_classes_CI_DIR}

( cd ${math_classes_CI_DIR} && make -j ${NJOBS} && make install )

# Setup Corn

git_checkout ${Corn_CI_BRANCH} ${Corn_CI_GITURL} ${Corn_CI_DIR}

( cd ${Corn_CI_DIR} && make -j ${NJOBS} && make install )

# Setup formal-topology

git_checkout ${formal_topology_CI_BRANCH} ${formal_topology_CI_GITURL} ${formal_topology_CI_DIR}

( cd ${formal_topology_CI_DIR} && make -j ${NJOBS} )
