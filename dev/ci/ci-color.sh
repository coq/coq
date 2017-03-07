#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

Color_CI_SVNURL=https://scm.gforge.inria.fr/anonscm/svn/color/trunk/color
Color_CI_DIR=${CI_BUILD_DIR}/color

svn checkout ${Color_CI_SVNURL} ${Color_CI_DIR}

( cd ${Color_CI_DIR} && make -j ${NJOBS} )
