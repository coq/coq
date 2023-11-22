#!/usr/bin/env bash

# This is the list of repositories used by the CI scripts, unless overridden
# by a call to the "overlay" function in ci-common

declare -a projects # the list of project repos that can be be overlayed

# checks if the given argument is a known project
function is_in_projects {
    for x in "${projects[@]}"; do
      if [ "$1" = "$x" ]; then return 0; fi;
    done
    return 1
}

# project <name> <giturl> <ref> [<archiveurl>]
#   [<archiveurl>] defaults to <giturl>/archive on github.com
#   and <giturl>/-/archive on gitlab
function project {

  local var_ref=${1}_CI_REF
  local var_giturl=${1}_CI_GITURL
  local var_archiveurl=${1}_CI_ARCHIVEURL
  local giturl=$2
  local ref=$3
  local archiveurl=$4
  case $giturl in
    *github.com*) archiveurl=${archiveurl:-$giturl/archive} ;;
    *gitlab*) archiveurl=${archiveurl:-$giturl/-/archive} ;;
  esac

  # register the project in the list of projects
  projects[${#projects[*]}]=$1

  # bash idiom for setting a variable if not already set
  : "${!var_ref:=$ref}"
  : "${!var_giturl:=$giturl}"
  : "${!var_archiveurl:=$archiveurl}"

}

########################################################################
# MathComp
########################################################################
project mathcomp "https://github.com/math-comp/math-comp" "master"

project mathcomp_1 "https://github.com/math-comp/math-comp" "mathcomp-1"

project fourcolor "https://github.com/math-comp/fourcolor" "master"

project oddorder "https://github.com/math-comp/odd-order" "master"

project mczify "https://github.com/math-comp/mczify" "master"

project finmap "https://github.com/math-comp/finmap" "cea9f088c9cddea1173bc2f7c4c7ebda35081b60"
# put back master when Analysis master moves to MathComp 2
# project finmap "https://github.com/math-comp/finmap" "master"

project bigenough "https://github.com/math-comp/bigenough" "master"

project analysis "https://github.com/math-comp/analysis" "master"

########################################################################
# UniMath
########################################################################
project unimath "https://github.com/UniMath/UniMath" "master"

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq "https://github.com/unicoq/unicoq" "master"

project mtac2 "https://github.com/Mtac2/Mtac2" "master"

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes "https://github.com/coq-community/math-classes" "master"

project corn "https://github.com/coq-community/corn" "master"

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""

project iris "https://gitlab.mpi-sws.org/iris/iris" ""

project autosubst "https://github.com/coq-community/autosubst" "master"

project iris_examples "https://gitlab.mpi-sws.org/iris/examples" "master"

########################################################################
# HoTT
########################################################################
project hott "https://github.com/HoTT/HoTT" "master"

########################################################################
# CoqHammer
########################################################################
project coqhammer "https://github.com/lukaszcz/coqhammer" "master"

########################################################################
# Flocq
########################################################################
project flocq "https://gitlab.inria.fr/flocq/flocq" "master"

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests "https://github.com/coq-community/coq-performance-tests" "master"

########################################################################
# coq-tools
########################################################################
project coq_tools "https://github.com/JasonGross/coq-tools" "master"

########################################################################
# Coquelicot
########################################################################
project coquelicot "https://gitlab.inria.fr/coquelicot/coquelicot" "master"

########################################################################
# CompCert
########################################################################
project compcert "https://github.com/AbsInt/CompCert" "master"

########################################################################
# VST
########################################################################
project vst "https://github.com/PrincetonUniversity/VST" "master"

########################################################################
# cross-crypto
########################################################################
project cross_crypto "https://github.com/mit-plv/cross-crypto" "master"

########################################################################
# rewriter
########################################################################
project rewriter "https://github.com/mit-plv/rewriter" "master"

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers "https://github.com/mit-plv/fiat" "master"

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto "https://github.com/mit-plv/fiat-crypto" "master"

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy "https://github.com/mit-plv/fiat-crypto" "sp2019latest"

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph "https://github.com/Karmaki/coq-dpdgraph" "coq-master"

########################################################################
# CoLoR
########################################################################
project color "https://github.com/fblanqui/color" "master"

########################################################################
# TLC
########################################################################
project tlc "https://github.com/charguer/tlc" "master-for-coq-ci"

########################################################################
# Bignums
########################################################################
project bignums "https://github.com/coq/bignums" "master"

########################################################################
# coqprime
########################################################################
project coqprime "https://github.com/thery/coqprime" "master"

########################################################################
# bbv
########################################################################
project bbv "https://github.com/mit-plv/bbv" "master"

########################################################################
# bedrock2
########################################################################
project bedrock2 "https://github.com/mit-plv/bedrock2" "tested"

########################################################################
# Coinduction
########################################################################
project coinduction "https://github.com/damien-pous/coinduction" "master"

########################################################################
# coq-lsp
########################################################################
project coq_lsp "https://github.com/ejgallego/coq-lsp" "main"

########################################################################
# Equations
########################################################################
project equations "https://github.com/mattam82/Coq-Equations" "main"

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi "https://github.com/LPCIC/coq-elpi" "coq-master"

project hierarchy_builder "https://github.com/math-comp/hierarchy-builder" "master"

########################################################################
# Engine-Bench
########################################################################
project engine_bench "https://github.com/mit-plv/engine-bench" "master"

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm "https://github.com/imdea-software/fcsl-pcm" "master"

########################################################################
# ext-lib
########################################################################
project ext_lib "https://github.com/coq-community/coq-ext-lib" "master"

########################################################################
# simple-io
########################################################################
project simple_io "https://github.com/Lysxia/coq-simple-io" "master"

########################################################################
# quickchick
########################################################################
project quickchick "https://github.com/QuickChick/QuickChick" "master"

########################################################################
# reduction-effects
########################################################################
project reduction_effects "https://github.com/coq-community/reduction-effects" "master"

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib "https://gitlab.inria.fr/fpottier/menhir" "master"

########################################################################
# coq-neural-net-interp
########################################################################
project neural_net_interp "https://github.com/JasonGross/neural-net-coq-interp" "tested"

########################################################################
# aac_tactics
########################################################################
project aac_tactics "https://github.com/coq-community/aac-tactics" "master"

########################################################################
# paco
########################################################################
project paco "https://github.com/snu-sf/paco" "master"

########################################################################
# coq-itree
########################################################################
project itree "https://github.com/DeepSpec/InteractionTrees" "master"

########################################################################
# coq-itree_io
########################################################################
project itree_io "https://github.com/Lysxia/coq-itree-io" "master"

########################################################################
# coq-ceres
########################################################################
project ceres "https://github.com/Lysxia/coq-ceres" "master"

########################################################################
# coq-parsec
########################################################################
project parsec "https://github.com/liyishuai/coq-parsec" "master"

########################################################################
# coq-json
########################################################################
project json "https://github.com/liyishuai/coq-json" "master"

########################################################################
# coq-async-test
########################################################################
project async_test "https://github.com/liyishuai/coq-async-test" "master"

########################################################################
# coq-http
########################################################################
project http "https://github.com/liyishuai/coq-http" "master"

########################################################################
# paramcoq
########################################################################
project paramcoq "https://github.com/coq-community/paramcoq" "master"

########################################################################
# relation_algebra
########################################################################
project relation_algebra "https://github.com/damien-pous/relation-algebra" "master"

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact "https://github.com/uwplse/StructTact" "master"

project inf_seq_ext "https://github.com/DistributedComponents/InfSeqExt" "master"

project cheerios "https://github.com/uwplse/cheerios" "master"

project verdi "https://github.com/uwplse/verdi" "master"

project verdi_raft "https://github.com/uwplse/verdi-raft" "master"

########################################################################
# stdlib2
########################################################################
project stdlib2 "https://github.com/coq/stdlib2" "master"

########################################################################
# argosy
########################################################################
project argosy "https://github.com/mit-pdos/argosy" "master"

########################################################################
# ATBR
########################################################################
project atbr "https://github.com/coq-community/atbr" "master"

########################################################################
# perennial
########################################################################
project perennial "https://github.com/mit-pdos/perennial" "coq/tested"
# PRs to fix Perennial failures should be submitted against the Perennial
# `master` branch. `coq/tested` is automatically updated every night to the
# `master` branch if CI on `master` is green. This is to avoid breaking Coq CI
# when Perennial CI breaks.

########################################################################
# metacoq
########################################################################
project metacoq "https://github.com/MetaCoq/metacoq" "main"

########################################################################
# SF suite
########################################################################
project sf "https://github.com/DeepSpec/sf" "master"

########################################################################
# Coqtail
########################################################################
project coqtail "https://github.com/whonore/Coqtail" "master"

########################################################################
# Deriving
########################################################################
project deriving "https://github.com/arthuraa/deriving" "master"

########################################################################
# VsCoq
########################################################################
project vscoq "https://github.com/coq-community/vscoq" "coq-master"

########################################################################
# category-theory
########################################################################
project category_theory "https://github.com/jwiegley/category-theory" "master"

########################################################################
# itauto
########################################################################
project itauto "https://gitlab.inria.fr/fbesson/itauto" "master"

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word "https://github.com/jasmin-lang/coqword" "v2.2"
# go back to "main" and change dependency to MC 2 when
# https://github.com/jasmin-lang/jasmin/pull/560 is merged

########################################################################
# Jasmin
########################################################################
project jasmin "https://github.com/jasmin-lang/jasmin" "main"

########################################################################
# Lean Importer
########################################################################
project lean_importer "https://github.com/SkySkimmer/coq-lean-import" "master"

########################################################################
# SerAPI
########################################################################
project serapi "https://github.com/ejgallego/coq-serapi" "main"

########################################################################
# SMTCoq
########################################################################
project smtcoq "https://github.com/smtcoq/smtcoq" "coq-master"

########################################################################
# Stalmarck
########################################################################
project stalmarck "https://github.com/coq-community/stalmarck" "master"

########################################################################
# coq-library-undecidability
########################################################################
project coq_library_undecidability "https://github.com/uds-psl/coq-library-undecidability" "master"

########################################################################
# Tactician
########################################################################
project tactician "https://github.com/coq-tactician/coq-tactician" "coqdev"

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler "https://github.com/SkySkimmer/coq-ltac2-compiler" "main"

########################################################################
# Waterproof
########################################################################
project waterproof "https://github.com/impermeable/coq-waterproof" "coq-master"
