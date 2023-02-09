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
project mathcomp 'https://github.com/math-comp/math-comp' '1f0daa44f834a040367f5fcb44451571fc9b646b'

project fourcolor 'https://github.com/math-comp/fourcolor' '4486796de0df716779caf4e1ba0741cb642dd28c'

project oddorder 'https://github.com/math-comp/odd-order' 'e400133ef20e446589b7c2c3c54c92429d5d89d6'

project mczify 'https://github.com/math-comp/mczify' '3db6ee0bc2bfd58b69e5d0fbb4cfb3a6152618bb'

project finmap 'https://github.com/math-comp/finmap' '17da86bf63acbf21924c9159a4b5c1d4a4e9b38c'

project bigenough 'https://github.com/math-comp/bigenough' 'ff71b25f31658d80fdae9657e8cf34e5e1052647'

project analysis 'https://github.com/math-comp/analysis' 'bfa6d4bc2fa548644b87769267ea49f523a21858'

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '75c3a38920088c3c5293ec3c1302cc67b3b8770e'

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' '98beb32a42f7425daaa78dccb1834b5c1ce49da2'

project mtac2 'https://github.com/Mtac2/Mtac2' '452241623a0315f4ee36c5b4fc2ee382d2d9563c'

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' 'e4b2d5cc6d53e45696d483231995969380914e8b'

project corn 'https://github.com/coq-community/corn' 'e34e331fa259c18192639ef3ce9e80cbf5db99dc'

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""

project iris "https://gitlab.mpi-sws.org/iris/iris" ""

project autosubst 'https://github.com/coq-community/autosubst' '495d547fa2a3e40da0f7d2a31469ac8caab058d2'

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' 'a2c0212f138de36b9c08f7ea6532f5a013bccd3a'

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' 'bca7ccfa0ca359feb11c17a09f45042b46b23b68'

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' 'd0c90dd6c04d1b91b191018c714b3c27bd9e64ee'

########################################################################
# GeoCoq
########################################################################
project geocoq 'https://github.com/GeoCoq/GeoCoq' '09a02dc56715b3308689843dd872209262beb5af'

########################################################################
# Flocq 3
########################################################################
project flocq3 'https://gitlab.inria.fr/flocq/flocq' '792f4a3a7715f6ee92020ad2de32e276bb6b3dca'

########################################################################
# Flocq (master)
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '0188199cb28d89a73937d009d935b016e2d394b5'

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' 'a45336158b6fc7a78a8add355461b141672fb0fe'

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' 'dbe8db0a40e63e48aa5811f9ec20857777c815de'

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' '929cd32e6ba4d3d6304385d87a6cc623f8fb3229'

########################################################################
# Gappa stand alone tool
########################################################################
project gappa_tool 'https://gitlab.inria.fr/gappa/gappa' '1ff88c212fbe63e97951d105a394d50fc6892af1'

########################################################################
# Gappa plugin
########################################################################
project gappa 'https://gitlab.inria.fr/gappa/coq' '8c5cc2fb439495103388019e3b2e3dd69fc0700a'

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' '318fc06823eb577e9b386aeea57133e8c3938ecf'

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' '3fc020420b3d05be8bde645ffce0f8295b1115fa'

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' '94f5d9d6b746a7e5baa4bed336948f0b851812b8'

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' '2c2d78e66ef475858bac47f4280049080bc968d7'

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' 'd5077586e33576294b4867b697122c247462ce15'

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' '9794ceb210ed9e3a39fe5eae8f4000748484bed1'

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' 'e34d1a3cdd08f1895835d4686a1b5d31a1a844c3'

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/Karmaki/coq-dpdgraph' 'c23162403322ac0e99e34018237a4b5bc7a7ba68'

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' '70f8d37fdaf8c4c973419e0475ccb32020530a30'

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' 'a56bc13dddf319d01b7da99a1fc90e5ac823e6b9'

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' 'def90f1bc835b938e894bbbec58758e56e8b8bea'

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' '12ad8645d2574dfced37ab4f9de8ea6459bb9048'

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' 'ee1630f3a8136f239de4dcbb3c59e350a392d7e8'

########################################################################
# bedrock2
########################################################################
project bedrock2 'https://github.com/mit-plv/bedrock2' '99b86e974bdaf0ed2ffd893b42cf60d980669000'

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' '610478f75358422673e2326e3a1d30d29d4e0dd2'

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' '521a9f5e89d82f575de4563334550bdaa759f308'

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' '4f6c4c5754f5cff6a2b3dd827eb56069d4d183a0'

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' 'd2cf8602d479b627c1f5d3d03044e8570af827ea'

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' '966458f9534fbf674ab068fa96ae335537ad50ff'

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' '4d87b5a93fa7aaf77428a5d7818ed7ba56809dce'

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' 'd68e6aa01859a938f39c07721e2f1328a2d8312b'

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' 'c318de88cd54119a1ff23696049ad7623704566b'

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' 'fc926669571e8315013eb0775e27f9653798b7f0'

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib "https://gitlab.inria.fr/fpottier/menhir" "20220210"

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' '2a2e1aad222be1496a281a743b97ff115b05473c'

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' '7f10f146f84591236f1ddccb0c75b56cedbdf34e'

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/ejgallego/paramcoq' '2f8e1988a7a605b78546c82238ea7eed3f38e3f6'

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' '00f84a00321ed87e84a723c34e177a59ccd8e230'

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
project stdlib2 'https://github.com/coq/stdlib2' '9dfc4b760ba4ec2ed08732d1fccc904b1f9189dc'

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' '24fb5441147e1b1ad9bf99716ab6c404d22276da'

########################################################################
# perennial
########################################################################
project perennial 'https://github.com/mit-pdos/perennial' '61a08b1bb46424b8a68153a49b528c825e829494'

########################################################################
# metacoq
########################################################################
project metacoq 'https://github.com/MetaCoq/metacoq' '42dba8651f40c30be9ce211e22a68c493b10dba1'

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' 'ff65c8725f7b5a1aeb1124bbaeb44a23faeb09d8'

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' '2fc990977e3ec0fb626b2004645c4180954584e0'

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' 'a6938be4eed0849e2d102fd3a9234e42d7014318'

########################################################################
# VsCoq
########################################################################
project vscoq 'https://github.com/maximedenes/vscoq' '9b9f52253f180143ec7b9c14083e1f0ae5608fb8'

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' 'e13d235c43bad45373de42ffef0ec5da71576c4f'

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' '2f88542cc7f723fb5450d300b5666933d2c9de7f'

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word 'https://github.com/jasmin-lang/coqword' 'd1372fe4f4ba733cf82b76ceef3252616fe20f1b'

########################################################################
# Jasmin
########################################################################
project jasmin 'https://github.com/jasmin-lang/jasmin' 'aee1b0db417c300610d4b505d1a7c4ff8ba62c3c'
