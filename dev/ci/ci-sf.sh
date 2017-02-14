#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

wget https://www.cis.upenn.edu/~bcpierce/sf/current/sf.tgz
tar xvfz sf.tgz

( cd sf && sed -i.bak 's/(K,N)/((K,N))/' LibTactics.v && make clean && make -j ${NJOBS} )


