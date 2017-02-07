#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git clone --depth 3 https://github.com/math-comp/math-comp.git

# coquelicot just needs mathcomp
( cd math-comp/mathcomp && \
  sed -i.bak '/ssrtest/d'   Make && \
  sed -i.bak '/odd_order/d'   Make && \
  sed -i.bak '/all\/all.v/d'  Make && \
  sed -i.bak '/character/d'   Make && \
  sed -i.bak '/real_closed/d' Make && \
  sed -i.bak '/solvable/d'    Make && \
  sed -i.bak '/field/d'       Make && \
  sed -i.bak '/fingroup/d'    Make && \
  sed -i.bak '/algebra/d'     Make && \
  make -j ${NJOBS} && make install )

# Setup ssr
# echo "Add ML Path \"`pwd`/math-comp/mathcomp/\"." > ${HOME}/.coqrc
# echo "Add LoadPath \"`pwd`/math-comp/mathcomp/\" as mathcomp." >> ${HOME}/.coqrc

# Setup coquelicot
git clone --depth 3 https://scm.gforge.inria.fr/anonscm/git/coquelicot/coquelicot.git

( cd coquelicot && ./autogen.sh && ./configure && ./remake -j${NJOBS} )
