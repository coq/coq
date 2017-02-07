#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git clone https://gforge.inria.fr/git/tlc/tlc.git

( cd tlc && make -j ${NJOBS} )
