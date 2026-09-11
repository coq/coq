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

# subproject <name> <parent project> <submodulefolder> <submodule giturl> <submodule branch>
# In the case of nested submodules, each subproject should be declared
# a subproject of its immediate parent, to ensure overlays are applied
# in the right order
function subproject {
  local var_parent_project=${1}_CI_PARENT_PROJECT
  local var_submodule_folder=${1}_CI_SUBMODULE_FOLDER
  local var_submodule_giturl=${1}_CI_SUBMODULE_GITURL
  local var_submodule_branch=${1}_CI_SUBMODULE_BRANCH
  local parent_project=$2
  local submodule_folder=$3
  local submodule_giturl=$4
  local submodule_branch=$5

  # register the project in the list of projects
  projects[${#projects[*]}]=$1

  : "${!var_parent_project:=$parent_project}"
  : "${!var_submodule_folder:=$submodule_folder}"
  : "${!var_submodule_giturl:=$submodule_giturl}"
  : "${!var_submodule_branch:=$submodule_branch}"
}

########################################################################
# MathComp
########################################################################
project mathcomp "https://github.com/math-comp/math-comp" "master"
# Contact @CohenCyril, @proux01 on github

project fourcolor "https://github.com/math-comp/fourcolor" "master"
# Contact @proux01 on github

project oddorder "https://github.com/math-comp/odd-order" "master"
# Contact @gares, @proux01 on github

project mczify "https://github.com/math-comp/mczify" "master"
# Contact @pi8027 on github

project finmap "https://github.com/math-comp/finmap" "master"
# Contact @CohenCyril on github

project bigenough "https://github.com/math-comp/bigenough" "master"
# Contact @CohenCyril on github

project analysis "https://github.com/math-comp/analysis" "master"
# Contact @affeldt-aist, @CohenCyril on github

########################################################################
# UniMath
########################################################################
project unimath "https://github.com/UniMath/UniMath" "master"
# Contact @benediktahrens, @m-lindgren, @nmvdw, @rmatthes on github

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq "https://github.com/unicoq/unicoq" "master"
# Contact @Janno, @mattam82 on github

project mtac2 "https://github.com/Mtac2/Mtac2" "master"
# Contact @Janno on github

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes "https://github.com/coq-community/math-classes" "master"
# Contact @Lysxia and @spitters on github

project corn "https://github.com/coq-community/corn" "master"
# Contact @Lysxia and @spitters on github

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris and
# iris_examples repos respectively. Those will be updated automatically within
# 24h after a change lands in stdpp or Iris. Ping @RalfJung and @robbertkrebbers
# if that does not work for some reason.
# The URL below is a mirror; use https://gitlab.mpi-sws.org/iris/stdpp for issues
# and PRs.
project stdpp "https://github.com/rocq-iris/stdpp" ""
# Contact @RalfJung, @robbertkrebbers on github

# The URL below is a mirror; use https://gitlab.mpi-sws.org/iris/iris for issues
# and PRs.
project iris "https://github.com/rocq-iris/iris" ""
# Contact @RalfJung, @robbertkrebbers on github

project autosubst "https://github.com/coq-community/autosubst" "master"
# Contact @RalfJung on github

# The URL below is a mirror; use https://gitlab.mpi-sws.org/iris/examples for
# issues and PRs.
project iris_examples "https://github.com/rocq-iris/examples" "master"
# Contact @RalfJung, @robbertkrebbers on github

########################################################################
# HoTT
########################################################################
project hott "https://github.com/HoTT/HoTT" "master"
# Contact @Alizter, @jdchristensen on github

########################################################################
# CoqHammer
########################################################################
project coqhammer "https://github.com/lukaszcz/coqhammer" "master"
# Contact @lukaszcz on github

########################################################################
# Flocq
########################################################################
project flocq "https://gitlab.inria.fr/flocq/flocq" "master"
# Contact @silene on github

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests "https://github.com/coq-community/coq-performance-tests" "master"
# Contact @JasonGross on github

########################################################################
# coq-tools
########################################################################
project coq_tools "https://github.com/JasonGross/coq-tools" "master"
# Contact @JasonGross on github

########################################################################
# Coquelicot
########################################################################
project coquelicot "https://gitlab.inria.fr/coquelicot/coquelicot" "master"
# Contact @silene on github

########################################################################
# CompCert
########################################################################
project compcert "https://github.com/AbsInt/CompCert" "master"
# Contact @xavierleroy on github

########################################################################
# VST
########################################################################
project vst "https://github.com/PrincetonUniversity/VST" "master"
# Contact @andrew-appel on github

########################################################################
# rewriter
########################################################################
project rewriter "https://github.com/mit-plv/rewriter" "master"
# Contact @JasonGross on github

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers "https://github.com/mit-plv/fiat" "master"
# Contact @JasonGross on github

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy "https://github.com/mit-plv/fiat-crypto" "sp2019latest"
# Contact @JasonGross on github

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto "https://github.com/mit-plv/fiat-crypto" "master"
# Contact @andres-erbsen, @JasonGross on github

# bedrock2, coqutil, rupicola
# fiat-crypto is not guaranteed to build with the latest version of
# bedrock2, so we use the pinned version of bedrock2 for fiat-crypto
# overlays do not have to follow suite
subproject rupicola fiat_crypto "rupicola" "https://github.com/mit-plv/rupicola" "master"
subproject bedrock2 rupicola "bedrock2" "https://github.com/mit-plv/bedrock2" "master"
subproject coqutil bedrock2 "deps/coqutil" "https://github.com/mit-plv/coqutil" "master"
# Contact @samuelgruetter, @andres-erbsen on github

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph "https://github.com/coq-community/coq-dpdgraph" "coq-master"
# Contact @Karmaki, @ybertot on github

########################################################################
# CoLoR
########################################################################
project color "https://github.com/fblanqui/color" "master"
# Contact @fblanqui on github

########################################################################
# Bignums
########################################################################
project bignums "https://github.com/coq/bignums" "master"
# Contact @erikmd, @proux01 on github

########################################################################
# coqprime
########################################################################
project coqprime "https://github.com/thery/coqprime" "master"
# Contact @thery on github

########################################################################
# Coinduction
########################################################################
project coinduction "https://github.com/damien-pous/coinduction" "master"
# Contact @damien-pous on github

########################################################################
# rocq-lsp
########################################################################
project rocq_lsp "https://github.com/rocq-community/rocq-lsp" "main"
# Contact @SkySkimmer on github

########################################################################
# Equations
########################################################################
project equations "https://github.com/rocq-prover/equations" "main"
# Contact @mattam82 on github

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi "https://github.com/LPCIC/coq-elpi" "master"
# Contact @gares on github

project hierarchy_builder "https://github.com/math-comp/hierarchy-builder" "master"
# Contact @CohenCyril, @gares on github

########################################################################
# Engine-Bench
########################################################################
project engine_bench "https://github.com/mit-plv/engine-bench" "master"
# Contact @JasonGross on github

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm "https://github.com/imdea-software/fcsl-pcm" "master"
# Contact @aleksnanevski, @clayrat on github

########################################################################
# ext-lib
########################################################################
project ext_lib "https://github.com/coq-community/coq-ext-lib" "master"
# Contact @liyishuai on github

########################################################################
# simple-io
########################################################################
project simple_io "https://github.com/Lysxia/coq-simple-io" "master"
# Contact @Lysxia, @liyishuai on github

########################################################################
# quickchick
########################################################################
project quickchick "https://github.com/QuickChick/QuickChick" "master"
# Contact @lemonidas, @Lysxia, @liyishuai on github

########################################################################
# reduction-effects
########################################################################
project reduction_effects "https://github.com/coq-community/reduction-effects" "master"
# Contact @liyishuai, @JasonGross on github

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib "https://gitlab.inria.fr/fpottier/menhir" "master"
# Contact @fpottier, @jhjourdan on github

########################################################################
# coq-neural-net-interp
########################################################################
project neural_net_interp "https://github.com/JasonGross/neural-net-coq-interp" "tested"
# Contact @JasonGross on github

########################################################################
# aac_tactics
########################################################################
project aac_tactics "https://github.com/coq-community/aac-tactics" "master"
# Contact @palmskog on github

########################################################################
# paco
########################################################################
project paco "https://github.com/snu-sf/paco" "master"
# Contact @damhiya on github

########################################################################
# coq-itree
########################################################################
project itree "https://github.com/DeepSpec/InteractionTrees" "master"
# Contact @Lysxia on github

########################################################################
# micromega-plugin
########################################################################
project micromega "https://github.com/rocq-community/micromega-plugin" "master"
# Contact @fajb, @proux01 on github

########################################################################
# paramcoq
########################################################################
project paramcoq "https://github.com/coq-community/paramcoq" "master"
# Contact @ppedrot on github

########################################################################
# relation_algebra
########################################################################
project relation_algebra "https://github.com/damien-pous/relation-algebra" "master"
# Contact @damien-pous on github

########################################################################
# Stdlib
########################################################################
project stdlib "https://github.com/coq/stdlib" "master"
# Contact TODO on github

########################################################################
# argosy
########################################################################
project argosy "https://github.com/mit-pdos/argosy" "master"
# Contact @tchajed on github

########################################################################
# ATBR
########################################################################
project atbr "https://github.com/coq-community/atbr" "master"
# Contact @palmskog, @tchajed on github

########################################################################
# metarocq
########################################################################
project metarocq "https://github.com/MetaRocq/metarocq" "main"
# Contact @mattam82, @yforster on github

########################################################################
# SF suite
########################################################################
project sf "https://github.com/DeepSpec/sf" "master"
# Contact @bcpierce00, @liyishuai on github

########################################################################
# Coqtail
########################################################################
project coqtail "https://github.com/whonore/Coqtail" "main"
# Contact @whonore on github

########################################################################
# Deriving
########################################################################
project deriving "https://github.com/arthuraa/deriving" "master"
# Contact @arthuraa on github

########################################################################
# VsRocq
########################################################################
project vsrocq "https://github.com/rocq-prover/vsrocq" "main"
# Contact @rtetley, @gares on github

########################################################################
# category-theory
########################################################################
project category_theory "https://github.com/jwiegley/category-theory" "master"
# Contact @jwiegley on github

########################################################################
# itauto
########################################################################
project itauto "https://gitlab.inria.fr/fbesson/itauto" "master"
# Contact @fajb on github

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word "https://github.com/jasmin-lang/coqword" "main"
# Contact @vbgl, @strub on github

########################################################################
# Jasmin
########################################################################
project jasmin "https://github.com/jasmin-lang/jasmin" "main"
# Contact @vbgl, @bgregoir on github

########################################################################
# Lean Importer
########################################################################
project lean_importer "https://github.com/coq-community/rocq-lean-import" "master"
# Contact @SkySkimmer on github

########################################################################
# SMTCoq
########################################################################
project smtcoq "https://github.com/smtcoq/smtcoq" "rocq-master"
# Contact @ckeller on github

########################################################################
# Stalmarck
########################################################################
project stalmarck "https://github.com/coq-community/stalmarck" "master"
# Contact @palmskog on github

########################################################################
# Tactician
########################################################################
project tactician "https://github.com/coq-tactician/coq-tactician" "coqdev"
# Contact @LasseBlaauwbroek on github

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler "https://github.com/SkySkimmer/coq-ltac2-compiler" "main"
# Contact @SkySkimmer on github

########################################################################
# Waterproof
########################################################################
project waterproof "https://github.com/impermeable/coq-waterproof" "coq-master"
# Contact @jellooo038, @jim-portegies on github

########################################################################
# Autosubst (2) OCaml
########################################################################
project autosubst_ocaml "https://github.com/uds-psl/autosubst-ocaml" "master"
# Contact @yforster on github

########################################################################
# Trakt
########################################################################
project trakt "https://github.com/rocq-trakt/trakt" "master"
# Contact @ckeller, @lafeychine on github

########################################################################
# MLtac2
########################################################################
project mltac2 "https://github.com/epfl-systemf/mltac2" "main"
# Contact @dhalilov on github
