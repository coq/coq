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
project mathcomp 'https://github.com/math-comp/math-comp' '4efe95e4b39cc058e63e9161d76f0b50af493c94'

project fourcolor 'https://github.com/math-comp/fourcolor' '4581901330cce906c3c58ce5c24e5d061ea3ab39'

project oddorder 'https://github.com/math-comp/odd-order' '91e3b9a75d12d142568985566e652988189a2ff4'

project mczify 'https://github.com/math-comp/mczify' '8481446a34ee53cf24639210877ed9f7dd1dcf92'

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '95d88e3c0b1c5ff05ce36e0deea02a5823ed404f'

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' '2095dff58b630dc69fa9b6d707e843e193fe18a8'

project mtac2 'https://github.com/Mtac2/Mtac2' 'd8332d81189f3763dfaccd9de31bc9f459fad6bb'

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' '5da1f4142c2db714d7943152e6522e56c95f434d'

project corn 'https://github.com/coq-community/corn' 'd6cbe5a1c5106078899b63a05bf0390c1f868337'

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""

project iris "https://gitlab.mpi-sws.org/iris/iris" ""

project autosubst 'https://github.com/coq-community/autosubst' 'c71b2dac46049d549fa002f59503091b2a0b99a8'

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' 'bb946806c5aa9bcb8184a8cb3bc1befecc0322a0'

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' 'd79c4bb3c0a10ceb8d8ff2acd4ffc4c645ffd5c9'

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' 'f8bd70509365f6e2c8038b773332eef935ca87ee'

########################################################################
# GeoCoq
########################################################################
project geocoq 'https://github.com/GeoCoq/GeoCoq' '25917f56a3b46843690457b2bfd83168bed1321c'

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' 'e68658cb2e6ed16c79fc4b01d578e79052f45bf8'

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' '5cc9a158e3aa32bc39716100e575f5f30cc72008'

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' 'd87641a8f0b19399c6a709796b62ae303dc11ac1'

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
project gappa 'https://gitlab.inria.fr/gappa/coq' '45c464f726a7361201f4902bfcbb0aaf46b15e3d'

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' '2198a280b1150a61be1e514f044da03e69a66af9'

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' '7f0d5bb642b886783f69add45dad9446c8ef4cd1'

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' 'b0e32790d17ec2836780e8e8f3c38f67366dda63'

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' 'dbc67ab8ca64fcc0e4c67d91afc9c68c7b9e096a'

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' 'cb85ee76ee3410f04333633f6644663ebb525ac8'

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' '79e021e7e38ed796138fab7231fedeef64691771'

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '9f540adc1b265732845fe0785efe89b3f8b3937f'

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/Karmaki/coq-dpdgraph' 'f1445af644340c1ca9b51dee98fddf4431c23635'

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' 'd6d57c65f5b898de7b93a916375a3b3cd0078914'

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' 'f5390a5ec9106b15b8f8a4434958d4959b15a295'

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' 'da002e1e296fff03dc6555a9687e7cc164547315'

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' '2ad3850655131aafb5b0e625b82069bc1573acaf'

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' 'd5ab9c04db85eb85688816dc687d118000a65736'

########################################################################
# bedrock2
########################################################################
project bedrock2 'https://github.com/mit-plv/bedrock2' 'ac173a934e8b64916d6e55868b57878d5b041b6f'

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' '722cccfe0fa4305c91bcdcce5ddc1fb43aa09cfe'

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' 'd1fca91261ff5dad68680b6bce14e3c2f13f31aa'

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' 'd3896f8ed5679a38509d9923a0ccf560d211fac3'

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' 'd2cf8602d479b627c1f5d3d03044e8570af827ea'

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' 'd68bef532d2c8ba6ff1edc80815f9ba9cd3f2d8c'

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' '8f0f0228332007a1b73abb01fb9bf828023007fa'

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' 'd0198042ac27a16ebf91aafc0b9bc163ac799a25'

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' 'e49fbf916fdc7b5949753928f689fa9334e11b1b'

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' '98b0279362f6e830588c2010bc6d150284cd6e3b'

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib "https://gitlab.inria.fr/fpottier/menhir" "20210310"

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' '70ab69806b188a742112e2c218fc40eeb44b5eeb'

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' '46bc4afb4e681d9942f3bae771b3e89923a251f0'

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' 'c951ffc65bc0d8c2d1e218b1888c7156d4535ad7'

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact 'https://github.com/uwplse/StructTact' '179bd5312e9d8b63fc3f4071c628cddfc496d741'

project inf_seq_ext 'https://github.com/DistributedComponents/InfSeqExt' 'd7a56b2ba532ac0a78a3e3ad0080d223186838de'

project cheerios 'https://github.com/uwplse/cheerios' '9c7f66e57b91f706d70afa8ed99d64ed98ab367d'

project verdi 'https://github.com/uwplse/verdi' '064cc4fb2347453bf695776ed820ffb5fbc1d804'

project verdi_raft 'https://github.com/uwplse/verdi-raft' 'ea99a7453c30a0c11b904b36a3b4862fad28abe1'

########################################################################
# stdlib2
########################################################################
project stdlib2 'https://github.com/coq/stdlib2' '54e057ea7023d058e57169a3bceaab708a5f7d26'

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' '9e8a6341b20f56855d829d6c0542258bb2c10037'

########################################################################
# perennial
########################################################################
project perennial 'https://github.com/mit-pdos/perennial' 'fb179c5f5ddc8e7a16efe5d65c826112732525db'

########################################################################
# metacoq
########################################################################
project metacoq 'https://github.com/MetaCoq/metacoq' 'b2e9f58336520d5c286af93941b6d603c21553ef'

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' 'd5fd1887ae7b23edea8f98cdf0b8c2db0ba874df'

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' 'f38e086135c5d9b69c9a5f70f82072419d952c29'

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' 'bc994b5950cc58f4eeb5a3d0fca60e7b6da9ab42'

########################################################################
# VsCoq
########################################################################
project vscoq 'https://github.com/maximedenes/vscoq' 'fe84907aaae2e7b1b9776e2876dd072bf8fd1320'

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' '1bd49317e9f2e27c3cca108768e57b2dc205d595'

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' '4a53bf249a10278e22c918136399eb0e66a6e173'
