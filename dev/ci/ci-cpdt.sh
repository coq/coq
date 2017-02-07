#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

wget http://adam.chlipala.net/cpdt/cpdt.tgz
tar xvfz cpdt.tgz

( cd cpdt && make clean && make -j ${NJOBS} )

