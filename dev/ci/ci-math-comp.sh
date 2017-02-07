#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git clone --depth 3 https://github.com/math-comp/math-comp.git

# odd_order takes too much time for travis.
( cd math-comp/mathcomp                              && \
     sed -i.bak '/PFsection/d'                  Make && \
     sed -i.bak '/stripped_odd_order_theorem/d' Make && \
     make Makefile.coq && make -f Makefile.coq -j ${NJOBS} all )
