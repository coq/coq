#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git_checkout master https://gforge.inria.fr/git/tlc/tlc.git tlc

( cd tlc && make -j ${NJOBS} )
