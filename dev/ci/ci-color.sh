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

# Adapt to PR #220 (FunInd not loaded in Prelude anymore)
sed -i -e "15i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/basis/ordered_set.v
sed -i -e "8i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/examples/cime_trace/equational_extension.v
sed -i -e "6i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/examples/cime_trace/more_list_extention.v
sed -i -e "6i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/examples/cime_trace/ring_extention.v
sed -i -e "27i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/list_extensions/dickson.v
sed -i -e "26i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/list_extensions/list_permut.v
sed -i -e "23i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/list_extensions/list_set.v
sed -i -e "25i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/list_extensions/list_sort.v
sed -i -e "21i From Coq Require Import FunInd." ${Color_CI_DIR}/Coccinelle/list_extensions/more_list.v
sed -i -e "21i From Coq Require Import FunInd." ${Color_CI_DIR}/Util/List/ListUtil.v
sed -i -e "17i From Coq Require Import FunInd." ${Color_CI_DIR}/Util/Multiset/MultisetOrder.v
sed -i -e "13i From Coq Require Import FunInd." ${Color_CI_DIR}/Util/Set/SetUtil.v

( cd ${Color_CI_DIR} && make )
