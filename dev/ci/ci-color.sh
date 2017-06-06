#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

Color_CI_DIR=${CI_BUILD_DIR}/color

# Setup Bignums

source ${ci_dir}/ci-bignums.sh

# Compiles CoLoR

svn checkout ${Color_CI_SVNURL} ${Color_CI_DIR}

sed -i -e "s/From Coq Require Import BigN/From Bignums Require Import BigN/" ${Color_CI_DIR}/Util/*/*.v
sed -i -e "s/From Coq Require Export BigN/From Bignums Require Export BigN/" ${Color_CI_DIR}/Util/*/*.v
sed -i -e "s/From Coq Require Import BigZ/From Bignums Require Import BigZ/" ${Color_CI_DIR}/Util/*/*.v
sed -i -e "s/From Coq Require Export BigZ/From Bignums Require Export BigZ/" ${Color_CI_DIR}/Util/*/*.v

( cd ${Color_CI_DIR} && make -j ${NJOBS} )
