#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

mathcomp_CI_DIR="${CI_BUILD_DIR}/math-comp"

checkout_mathcomp "${mathcomp_CI_DIR}"

# odd_order takes too much time for travis.
( cd "${mathcomp_CI_DIR}/mathcomp"                  && \
  sed -i.bak '/PFsection/d'                  Make && \
  sed -i.bak '/stripped_odd_order_theorem/d' Make && \
  make Makefile.coq && make -f Makefile.coq all )
