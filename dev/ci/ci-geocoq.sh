#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

# XXX: replace by generic template
GeoCoq_CI_BRANCH=master
GeoCoq_CI_GITURL=https://github.com/GeoCoq/GeoCoq.git

git clone --depth 1 -b ${GeoCoq_CI_BRANCH} ${GeoCoq_CI_GITURL}

( cd GeoCoq && ./configure.sh && make -j ${NJOBS} )
