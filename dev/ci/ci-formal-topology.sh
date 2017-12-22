#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

formal_topology_CI_DIR=${CI_BUILD_DIR}/formal-topology

git_checkout ${formal_topology_CI_BRANCH} ${formal_topology_CI_GITURL} ${formal_topology_CI_DIR}

( cd ${formal_topology_CI_DIR} && make )
