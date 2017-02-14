#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

svn checkout https://scm.gforge.inria.fr/anonscm/svn/color/trunk/color color

( cd color && make -j ${NJOBS} )
