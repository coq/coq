#!/usr/bin/env bash

set -xe

# Coq's tools need an ending slash :S, we should fix them.
export COQBIN=`pwd`/bin/
export PATH=`pwd`/bin:$PATH

ls `pwd`/bin

# Maybe we should just use Ruby...
mathcomp_CI_BRANCH=master
mathcomp_CI_GITURL=https://github.com/math-comp/math-comp.git

# Where we clone and build external developments
CI_BUILD_DIR=`pwd`/_build_ci

# git_checkout branch
git_checkout()
{
  local _BRANCH=${1}
  local _URL=${2}
  local _DEST=${3}

  mkdir -p ${CI_BUILD_DIR}
  cd ${CI_BUILD_DIR}

  if [ ! -d ${_DEST} ] ; then
    echo "Checking out ${_DEST}"
    git clone --depth 1 -b ${_BRANCH} ${_URL} ${_DEST}
  fi
  ( cd ${_DEST} && git pull &&
    echo "${_DEST}: `git log -1 --format='%s | %H | %cd | %aN'`" )
}

checkout_mathcomp()
{
  git_checkout ${mathcomp_CI_BRANCH} ${mathcomp_CI_GITURL} ${1}
}

# this installs just the ssreflect library of math-comp
install_ssreflect()
{
  echo 'Installing ssreflect' && echo -en 'travis_fold:start:ssr.install\\r'

  checkout_mathcomp math-comp
  ( cd math-comp/mathcomp            && \
    sed -i.bak '/ssrtest/d'     Make && \
    sed -i.bak '/odd_order/d'   Make && \
    sed -i.bak '/all\/all.v/d'  Make && \
    sed -i.bak '/character/d'   Make && \
    sed -i.bak '/real_closed/d' Make && \
    sed -i.bak '/solvable/d'    Make && \
    sed -i.bak '/field/d'       Make && \
    sed -i.bak '/fingroup/d'    Make && \
    sed -i.bak '/algebra/d'     Make && \
    make Makefile.coq && make -f Makefile.coq -j ${NJOBS} all && make install )

  echo -en 'travis_fold:end:ssr.install\\r'

}
