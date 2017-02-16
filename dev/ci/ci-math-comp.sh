#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

checkout_mathcomp math-comp

# odd_order takes too much time for travis.
( cd math-comp/mathcomp                           && \
  sed -i.bak '/PFsection/d'                  Make && \
  sed -i.bak '/stripped_odd_order_theorem/d' Make && \
  make Makefile.coq && make -f Makefile.coq -j ${NJOBS} all )
