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
project mathcomp 'https://github.com/math-comp/math-comp' '6dc4a759117dc29092208d6f175289cf0274bae2'

project fourcolor 'https://github.com/math-comp/fourcolor' 'd6127d4e02fdb141131f3aa07fa4d3d4baf71529'

project oddorder 'https://github.com/math-comp/odd-order' '833261a01fd0c62b05ccbadfc0c682e0bc16a5e9'

project mczify 'https://github.com/math-comp/mczify' '5d6abf13b137d8499e59b12e7e216f7cc12304e2'

project finmap 'https://github.com/math-comp/finmap' '27563c3d10289e7118f1ae5d40fb1f3e0b8a55ff'

project bigenough 'https://github.com/math-comp/bigenough' 'ff71b25f31658d80fdae9657e8cf34e5e1052647'

project analysis 'https://github.com/math-comp/analysis' '38ada1e74e69e2d8a3959c7c20cc4e5d1c85c496'

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '0df0949b951e198c461e16866107a239c8bc0a1e'

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' '0c33033e921c8f7f9dcc47078f0de7a4a0c99999'

project mtac2 'https://github.com/Mtac2/Mtac2' 'c7ae44d4d2af65e9d57bb80b8b70ac0b30c3fe93'

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' '754ddc768299afdf6274d03d713907d4d0282361'

project corn 'https://github.com/coq-community/corn' 'd4e6db77c5082e62a643f19105d6e7ee5547df29'

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""

project iris "https://gitlab.mpi-sws.org/iris/iris" ""

project autosubst 'https://github.com/coq-community/autosubst' '495d547fa2a3e40da0f7d2a31469ac8caab058d2'

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' '7b79d6e2fdbf0cedd80b9346da8b4fc9e7aaa424'

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' '3fcad92c7686345f1037cb833146b3963aabd9d8'

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '4ac485677e2a313279fc64829f1963d92e0ca154'

########################################################################
# GeoCoq
########################################################################
project geocoq 'https://github.com/GeoCoq/GeoCoq' '09a02dc56715b3308689843dd872209262beb5af'

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '3c92e3f9461c382d95f43e04815c0070be687335'

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' '4aaef74e5742fe3ad87c5d18d735e82b1284ecc6'

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' '1f1c77c9e24de645418fd476493e48d6d930a69e'

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' '9f6f576844a53c930609883a2850f109fb76e965'

########################################################################
# CompCert
########################################################################
project compcert "https://github.com/AbsInt/CompCert" "5be9ae2235b16239f023a36679b7d515dd774c68"

########################################################################
# VST
########################################################################
project vst "https://github.com/PrincetonUniversity/VST" "d635e62a083ad78c16548c29904c527a74f7b1e5"

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' '27d253a606e62a4746571ae026c08ce6c170efff'

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' 'de56173b42be33ea3bcf4f96a491bd5c2b30892e'

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' 'ddb9d1c56c47e684f52272a2d6cc71749a010903'

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto "https://github.com/mit-plv/fiat-crypto" "671cf2894c3d72a145d4cc9193f8108b61a8d402"

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '1fce11eade067afa33d08f2cc7596d0fb68afa1a'

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/Karmaki/coq-dpdgraph' 'fbbf464f9a164d915d433015fee32c3ace7c257d'

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' '4ebc8c56901fa79decea4661eb698267d7e5d050'

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' 'f4835e72393f84892c8bbf9246cae1dd7e5cde5d'

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' 'def90f1bc835b938e894bbbec58758e56e8b8bea'

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' '762c7f5e8c5fa13c85020d5b24b7910843266f00'

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' '18c77dac3535e71a47e3cc27efc82a76169879aa'

########################################################################
# bedrock2
########################################################################
project bedrock2 'https://github.com/mit-plv/bedrock2' '16c1ac1b717ec833d3d32963660fa91a4169ea2f'

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' '80767d571837914218bcde040c3071a483f75a72'

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' '9448eb21d3f8a3b663dbe7f85e7efa7bb1722400'

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' 'ccf9db17d0457268e7dac0f0ee17003cd95f5a77'

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' '8c0b15abc38b1d3f7dc606f4eeef9fba1a986b05'

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' 'a654207feab3c08150ae79ac929883fd04ef0191'

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' 'd48e6583c4fe01479f743ea21d9b921073cb3f5b'

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' '403db47e0b96222cd3c89c48ed5f8da10319da77'

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' '81d8ffe90d6934ccbadb0c1468f8c3bc3627cc81'

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
project aac_tactics 'https://github.com/coq-community/aac-tactics' '6e02fa08c62f38164aae355fe49fe6b923f04323'

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' '4f140d2083632e069e9f0f0cdd82171b60daf0de'

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' '308614a72e89ee62cdd0d98a28d8fc4812f58324'

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' '649a44282b19864a4aec28bcaa5453da1b9512df'

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact 'https://github.com/uwplse/StructTact' '2ba456d80a1422bfed3e46524e8f56b436b1bd4a'

project inf_seq_ext 'https://github.com/DistributedComponents/InfSeqExt' '41f02fefeb550d453be777fd246564f300835785'

project cheerios 'https://github.com/uwplse/cheerios' '48bdcefec49916116a418300672b0bd028ff91db'

project verdi 'https://github.com/uwplse/verdi' '26f1f4de5aeaa7043978cc18b3a30834818f484c'

project verdi_raft 'https://github.com/uwplse/verdi-raft' 'ce31a56f33949c9ac0d88e5bc0f7d84fded1d68f'

########################################################################
# stdlib2
########################################################################
project stdlib2 'https://github.com/coq/stdlib2' '9dfc4b760ba4ec2ed08732d1fccc904b1f9189dc'

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' 'a6a5aa0d3868efd4ada0b40927b5748e5d8967d3'

########################################################################
# perennial
########################################################################
project perennial 'https://github.com/mit-pdos/perennial' 'aac2736b67c16b9abf71692086c19f6501ed9afa'

########################################################################
# metacoq
########################################################################
project metacoq 'https://github.com/MetaCoq/metacoq' '859fdccf985c348fe7ee6bf36a9ab0c34410d723'

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' '9f5fb840950dcf54cc4ce0884ffb75c62f9bcd6a'

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' '98c99cc950f147a877d56a590d92b357c24086b9'

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' 'c86a0a39ff7e360da52a996d1b2b600e5fd646db'

########################################################################
# VsCoq
########################################################################
project vscoq 'https://github.com/maximedenes/vscoq' 'ce56385daed08a2a25130f9696d8c5f03fd94653'

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' '17f1254d0254afb4f8cc20ea561168a07627d4ee'

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' '5b291966e48bd6f2e933977ad45d4d82b0672ae3'

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word 'https://github.com/jasmin-lang/coqword' '9012f08c33a8c0d3b65e6e9494fd792522bf7b5c'

########################################################################
# Jasmin
########################################################################
project jasmin 'https://github.com/jasmin-lang/jasmin' '9935aaace97f8bc3fe5c12c787432b8308605c64'

########################################################################
# Lean Importer
########################################################################
project lean_importer 'https://github.com/SkySkimmer/coq-lean-import' '9e9c13e8b27fd9ba1b5258e89f7c862d36953079'

########################################################################
# SerAPI
########################################################################
project serapi 'https://github.com/ejgallego/coq-serapi' 'acb183d1a5023a14025cf4b3fcc5430a6194a250'

########################################################################
# SMTCoq
########################################################################
project smtcoq 'https://github.com/smtcoq/smtcoq' 'a8ab8231397ce7455826204a96991935c9efc0e0'

########################################################################
# Stalmarck
########################################################################
project stalmarck 'https://github.com/coq-community/stalmarck' '99fb0fd50c2f6230d29a412f7091013c03bf8a58'
