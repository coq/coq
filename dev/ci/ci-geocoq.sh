#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

# XXX: replace by generic template
GeoCoq_CI_BRANCH=master
GeoCoq_CI_GITURL=https://github.com/GeoCoq/GeoCoq.git

git_checkout ${GeoCoq_CI_BRANCH} ${GeoCoq_CI_GITURL} GeoCoq

( cd GeoCoq                                               && \
  ./configure.sh                                          && \
  sed -i.bak '/Ch16_coordinates_with_functions\.v/d' Make && \
  sed -i.bak '/Elements\/Book_1\.v/d'                Make && \
  sed -i.bak '/Elements\/Book_3\.v/d'                Make && \
  coq_makefile -f Make -o Makefile                        && \
  make -j ${NJOBS} )
