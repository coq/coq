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
project mathcomp 'https://github.com/math-comp/math-comp' '10816c7d830a568d732c749831466ba8830ffe49'

project fourcolor 'https://github.com/math-comp/fourcolor' '4581901330cce906c3c58ce5c24e5d061ea3ab39'

project oddorder 'https://github.com/math-comp/odd-order' '91e3b9a75d12d142568985566e652988189a2ff4'

project mczify 'https://github.com/math-comp/mczify' 'a1cca0ee6aba5d0a932d43888cc814cdf620784d'

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' 'd0e7d748fb5cee00472c08abe1835022910ec7ff'

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' '5ed1cdf38a7ccc4d5f3f4d83c7855c41e0f855e8'

project mtac2 'https://github.com/Mtac2/Mtac2' 'c27161ba0e9c750976f343cae3245708580c8079'

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' 'b94b24aa387abb90740acf7cc24286bf27d0fb50'

project corn 'https://github.com/coq-community/corn' 'c366d3f01ec1812b145117a4da940518b092d3a6'

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""

project iris "https://gitlab.mpi-sws.org/iris/iris" ""

project autosubst 'https://github.com/coq-community/autosubst' 'd1a90313f321a06ca96b7f453b3de8296dc914dc'

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' 'ee6a36b3e803ebec465bf44bb5bcbf9b19fe6b62'

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' '8f17cbee7274578a27606953b6da576b22c1ea0d'

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '1079879790f671389e282a3606c0eda996b6c16a'

########################################################################
# GeoCoq
########################################################################
project geocoq 'https://github.com/GeoCoq/GeoCoq' '1786a9a33dbca21e466e3ba57afaaa78876d1721'

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '239727fc0669d76ee60a45efb176bda2fe261f58'

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' 'ae8385b9471409387d0f47f01e38b866ba70bda1'

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' '366c217bf1d7b158d0c1721d7e8f254f025f89a4'

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' '09eb630f233c6887bef8f6764c7145bc45f24951'

########################################################################
# Gappa stand alone tool
########################################################################
project gappa_tool 'https://gitlab.inria.fr/gappa/gappa' '6c97a36257369d89ff32c9877c0e83681bfd3df9'

########################################################################
# Gappa plugin
########################################################################
project gappa 'https://gitlab.inria.fr/gappa/coq' 'f32711d1395a590492d9419a59ce0f9707765c4b'

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' 'a0ad5ff6f9c7603610a7448935b36c9ed22c6435'

########################################################################
# VST
########################################################################
# todo: 2021 03 11: switch back to master once vst merges the compcert3.9 branch
project vst 'https://github.com/PrincetonUniversity/VST' '0da1e909bdbe458af24148c5d681be1be09942e2'

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' 'c7cc46de53cf6b2363631a3b17b2ab12ce42e2f8'

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' '7553a6d910b7846e778fd648adc14f7395d2b3c9'

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' '490532505f20d3c93e0936f5770d2358c6effaaf'

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' 'f549083118b817dca59d435c18b83179aa06bd9a'

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '093ea19d246a3a79d019b5a78606559b261cf7c1'

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/Karmaki/coq-dpdgraph' '3f8a02e32487b66d168a59f5c24450531ee3a632'

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' '1e7b26553c1ca94c787ad5a1b938acabb8d47f2f'

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' 'f5390a5ec9106b15b8f8a4434958d4959b15a295'

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' 'a419f649a7a34e28049f3f18a5ee4068c2cd7fff'

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' 'd4bcfa8f7d7bdbe879d842ecfe575406f622c8ae'

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' '1386458cdf0b87bd9deaa2cdc47d3d732f96f5b6'

########################################################################
# bedrock2
########################################################################
project bedrock2 'https://github.com/mit-plv/bedrock2' '76ad54ba0704cc589d7c121b0e16b53ad3ea8b75'

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' '3b48ad15c64fe1f3ec81978679960f265a7877b5'

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' '60db122c8009b04f1bc44c2466a737e55ebe4b6a'

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' 'bd589b63bf48cf9a00812bdaa0c9a8192e78b83b'

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' '45f456e4c3b37704c6ff83ef072dc1260fef8f43'

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' 'cbd73130489169d1bb236a0888fceacaa77f0d70'

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' '968fb49a1f1044adf87f8e427cbe2d83d525d37d'

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' 'f7536c629dd02883abb5a2d64865becafed3af5b'

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' '80f4c88e949f25b6167993ce6a7e34ed29ca44cb'

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' '7cf41546f2d15ea3a4eeeb68695b288db2d9e09a'

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib "https://gitlab.inria.fr/fpottier/menhir" "20210310"

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' '16d30aba89ec4f5a7663ff31ac1b81212dd22e9a'

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' '1d9409b9eb56cb3f60e176e1f9194d6c4e09afef'

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' '7c37b9284848f39091770a60920fcc90a0019b47'

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact 'https://github.com/uwplse/StructTact' '179bd5312e9d8b63fc3f4071c628cddfc496d741'

project inf_seq_ext 'https://github.com/DistributedComponents/InfSeqExt' 'd7a56b2ba532ac0a78a3e3ad0080d223186838de'

project cheerios 'https://github.com/uwplse/cheerios' '9c7f66e57b91f706d70afa8ed99d64ed98ab367d'

project verdi 'https://github.com/uwplse/verdi' '54597d8ac7ab7dd4dae683f651237644bf77701e'

project verdi_raft 'https://github.com/uwplse/verdi-raft' 'dbf3084f8a741d56b5d05a87e39705329753bb6e'

########################################################################
# stdlib2
########################################################################
project stdlib2 'https://github.com/coq/stdlib2' '54e057ea7023d058e57169a3bceaab708a5f7d26'

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' '63dd6e6d046e3dde072ae1b6862639a8f62b1213'

########################################################################
# perennial
########################################################################
project perennial 'https://github.com/mit-pdos/perennial' '8d8e50d7c2cdf587bded3a3dbca9af26333dcf5f'

########################################################################
# metacoq
########################################################################
project metacoq 'https://github.com/MetaCoq/metacoq' '52950970c23eec013e91346e9237e693b6debec3'

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' '41c4ddd76dbde6a7aede634d7b003a64b5b11e98'

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' 'aa817559be68d9e90316bc7e5d3205fe2ffcffbe'

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' 'fa62caa5bd55431d42c3d6ed88bfc00899413dce'

########################################################################
# VsCoq
########################################################################
project vscoq 'https://github.com/maximedenes/vscoq' 'f6f61c52d7e01b18dd4fea19604ee0a2bf1be22c'
