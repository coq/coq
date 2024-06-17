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
project mathcomp 'https://github.com/math-comp/math-comp' 'd15522db878ddab2f17669d20159126b6274dd1a'
# Contact @CohenCyril, @proux01 on github

project mathcomp_1 "https://github.com/math-comp/math-comp" "a526d8dc7956ce1c1bc88051d0656d35b76608a3"
# Contact @CohenCyril, @proux01 on github

project fourcolor 'https://github.com/math-comp/fourcolor' '91ff6b8b846c8ad683260a5e6ce400e186f43c6e'
# Contact @ybertot, @proux01 on github

project oddorder 'https://github.com/math-comp/odd-order' '8dbbae0e53a6d1fcf3471c8fae4dd14c8f18bd93'
# Contact @gares, @proux01 on github

project mczify 'https://github.com/math-comp/mczify' '3ea1c2d2baebf1c7b0bcc4ba74825da1d27901a8'
# Contact @pi8027 on github

project finmap 'https://github.com/math-comp/finmap' 'a907a9e160a3ce0a546934a36016e75a05c73f3f'
# Contact @CohenCyril on github

project bigenough 'https://github.com/math-comp/bigenough' 'ff71b25f31658d80fdae9657e8cf34e5e1052647'
# Contact @CohenCyril on github

project analysis 'https://github.com/math-comp/analysis' '9c311a9344f3af02fbb12101b24482846d64e8ea'
# Contact @affeldt-aist, @CohenCyril on github

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '05b0156b527423f980c493317a766d665b5e1401'
# Contact @benediktahrens, @m-lindgren, @nmvdw, @rmatthes on github

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' '88f3964f4db12910b53f213ad7fcb6f868f76548'
# Contact @beta-ziliani, @Janno, @mattam82 on github

project mtac2 'https://github.com/Mtac2/Mtac2' 'caa52a1e21c5368105f4ab8e9f4bf3235aedfa7c'
# Contact @beta-ziliani, @Janno, @mattam82 on github

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' '2a8e12360cceee510f39e3ef4d0a7472d70fa684'
# Contact @spitters on github

project corn 'https://github.com/coq-community/corn' '5e74c2920f76c9888e70dba466b92787dcf0d077'
# Contact @spitters on github

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris and
# iris_examples repos respectively. So just getting a fix landed in stdpp or
# Iris is not enough. Ping @RalfJung and @robbertkrebbers if you need the
# versions of stdpp or Iris to be bumped. Perennial also has its own pinned
# versions of stdpp and Iris; ping @tchajed and @zeldovich to get that bumped.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""
# Contact @RalfJung, @robbertkrebbers on github

project iris "https://gitlab.mpi-sws.org/iris/iris" ""
# Contact @RalfJung, @robbertkrebbers on github

project autosubst 'https://github.com/coq-community/autosubst' '6ba0acccef68c75f6cca8928706c726754d69791'
# Contact @RalfJung, @co-dan on github

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' 'e17e7e92f0a0f52dce65e1189d7c32fa20c23815'
# Contact @RalfJung, @robbertkrebbers on github

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' '5661e6850709f6f56e2a80fc3dc2d72498780758'
# Contact @Alizter, @jdchristensen on github

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '7dcbc6ad043c4fef109906ad4cbc623c8e343a87'
# Contact @lukaszcz on github

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '561210b49466c1a0f911f6051fa50653e3fc6ca0'
# Contact @silene on github

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' 'd1fb22459af24d77b0ab0c224403cfd942f37fe9'
# Contact @JasonGross on github

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' '1c520114230875e0dbb00216d868391a338febaf'
# Contact @JasonGross on github

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' 'ca1a747aa8b7ccbfa67a55ae5c8e5c8df71cc396'
# Contact @silene on github

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' '2ca39a2801d333abcfa3d691620d03abde4e7e37'
# Contact @xavierleroy on github

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' '0eed04f85ecfa9607d200b37aa69ac0fb39a1071'
# Contact @andrew-appel on github

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' '208894a6efd2fe952eb384918cf38403e8a7cc15'
# Contact @andres-erbsen on github

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' 'edcec730f68469475fdc4b78495ae941a5b320ec'
# Contact @JasonGross on github

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' '33cee618160f76e7b15ea3e0db02f8198df347a5'
# Contact @JasonGross on github

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '9ace037e9c48960853ff597ba506ee25abb39789'
# Contact @JasonGross on github

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' '7ff747f57d44c7e9ffe3302c647dc96b3f203c7b'
# Contact @andres-erbsen, @JasonGross on github

# bedrock2, coqutil, rupicola, kami, riscv_coq
# fiat-crypto is not guaranteed to build with the latest version of
# bedrock2, so we use the pinned version of bedrock2 for fiat-crypto
# overlays do not have to follow suite
subproject rupicola fiat_crypto "rupicola" "https://github.com/mit-plv/rupicola" "71a5a07a837baeb90c4cec554c0462fa48194f04"
subproject bedrock2 rupicola "bedrock2" "https://github.com/mit-plv/bedrock2" "6fcb247abe8480600e3ddd1b0de1d5d7e628d772"
subproject coqutil bedrock2 "deps/coqutil" "https://github.com/mit-plv/coqutil" "126561ce8d32df8be7ea7de10eebd0e35b9fa8e9"
subproject kami bedrock2 "deps/kami" "https://github.com/mit-plv/kami" "de880ce21dc927b050e33e803c903238978f8021"
subproject riscv_coq bedrock2 "deps/riscv-coq" "https://github.com/mit-plv/riscv-coq" "d0afd4b58178976a2887c07e4f05c15d757fa0fc"
# Contact @samuelgruetter, @andres-erbsen on github

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/coq-community/coq-dpdgraph' '83711f445936dc8a2d09581edccece934d34a8d4'
# Contact @Karmaki, @ybertot on github

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' 'b063daf21dc89734c999cbb0893ae25830f1d0f4'
# Contact @fblanqui on github

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' 'd060155ce52e95c2bf450519f00b2f073732a588'
# Contact @charguer on github

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' 'da802e5c9469e4e13d0a1c22ed98092037b77010'
# Contact @erikmd, @proux01 on github

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' '6c225a2060ef2a47bdd487bca775f21bfe1fa5de'
# Contact @thery on github

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' 'c53d5b95c70839ae8e947010d85503bd1ada1120'
# Contact @JasonGross, @samuelgruetter on github

########################################################################
# Coinduction
########################################################################
project coinduction 'https://github.com/damien-pous/coinduction' '421077f5de6f5094d656f0f272317b57ee82f83f'
# Contact @damien-pous on github

########################################################################
# coq-lsp
########################################################################
project coq_lsp 'https://github.com/ejgallego/coq-lsp' 'ad2040fa33a741afd30183050ad3b53bf5eb1366'
# Contact @ejgallego on github

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' 'f9f7d3cdf91bae89f255335e083e9ddd5325f8df'
# Contact @mattam82 on github

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' '92de5c8f8fc58b207f0a23a52edabc614425bd93'
# Contact @gares on github

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' '8b1725c9d99e2f0ce6514998b125706aaeb550ac'
# Contact @CohenCyril, @gares on github

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' '8c0b15abc38b1d3f7dc606f4eeef9fba1a986b05'
# Contact @JasonGross on github

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' '6f462300ae8a6f98b1407652943d3ac74e6f2b88'
# Contact @aleksnanevski, @clayrat on github

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' 'b1fa2800a867df12eaced8ad324a04c2ada12a5a'
# Contact @gmalecha, @liyishuai on github

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' 'b4f11fb9481fbc43c481112e096dd4bab85d8b2f'
# Contact @Lysxia, @liyishuai on github

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' 'b7c8bb7545a7dd435696033153d43d32f62f323e'
# Contact @lemonidas, @Lysxia, @liyishuai on github

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' 'f0570f498bc8a0d25e878115b4066b140908c4b4'
# Contact @liyishuai, @JasonGross on github

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib 'https://gitlab.inria.fr/fpottier/menhir' '8a424e9842f2ea3e68caaf79e0741bad122ee14f'
# Contact @fpottier, @jhjourdan on github

########################################################################
# coq-neural-net-interp
########################################################################
project neural_net_interp 'https://github.com/JasonGross/neural-net-coq-interp' 'dc100dd8b5858407607acc83ea896cf781375173'
# Contact @JasonGross on github

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' 'aa70a2d40b4bf659cccc187b25cff03a08f5a63f'
# Contact @palmskog on github

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' '5c5693f46c8957f36a2349a0d906e911366136de'
# Contact @minkiminki on github

########################################################################
# coq-itree
########################################################################
project itree 'https://github.com/DeepSpec/InteractionTrees' 'e7fed212b1061b358428b57e11ee489184e241a2'
# Contact @Lysxia on github

########################################################################
# coq-itree_io
########################################################################
project itree_io 'https://github.com/Lysxia/coq-itree-io' 'af0326793a19f142eba800dba6044143b108ceaa'
# Contact @Lysxia, @liyishuai on github

########################################################################
# coq-ceres
########################################################################
project ceres 'https://github.com/Lysxia/coq-ceres' 'f61b24d48222db0100de19f88c19151a3aeb826f'
# Contact @Lysxia on github

########################################################################
# coq-parsec
########################################################################
project parsec 'https://github.com/liyishuai/coq-parsec' '2efb4437f8451dfbeb174368f860e629135c08ab'
# Contact @liyishuai on github

########################################################################
# coq-json
########################################################################
project json 'https://github.com/liyishuai/coq-json' '71974c15819ade300bcff5d9aa62cb0774387c4d'
# Contact @liyishuai on github

########################################################################
# coq-async-test
########################################################################
project async_test 'https://github.com/liyishuai/coq-async-test' '0637b95ae52060d8a808261ca97890d03c9a4503'
# Contact @liyishuai on github

########################################################################
# coq-http
########################################################################
project http 'https://github.com/liyishuai/coq-http' 'cabde79a4a0d978d031475c7443be7fd43a711c5'
# Contact @liyishuai on github

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' '7db5cb1ae8f330365548bb576c6928c803645885'
# Contact @proux01 on github

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' 'dbb5713ab490fdfabc87785e0f17370edce7723f'
# Contact @damien-pous on github

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact 'https://github.com/uwplse/StructTact' '97268e11564c8fe59aa72b062478458d7aa53e9d'
# Contact @palmskog on github

project inf_seq_ext 'https://github.com/DistributedComponents/InfSeqExt' '601e89ec019501c48c27fcfc14b9a3c70456e408'
# Contact @palmskog on github

project cheerios 'https://github.com/uwplse/cheerios' '5c9318c269f9cae1c1c6583a44405969ac0be0dd'
# Contact @palmskog on github

project verdi 'https://github.com/uwplse/verdi' 'b7f77848819878b1faf0e2e6a730f9bb850130be'
# Contact @palmskog on github

project verdi_raft 'https://github.com/uwplse/verdi-raft' 'a3375e867326a82225e724cc1a7b4758b029376f'
# Contact @palmskog on github

########################################################################
# stdlib2
########################################################################
project stdlib2 'https://github.com/coq/stdlib2' '33212e05c51efa012c9dfccd0b9e735a42f2d924'
# Contact @maximedenes, @vbgl on github

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' 'a6a5aa0d3868efd4ada0b40927b5748e5d8967d3'
# Contact @tchajed on github

########################################################################
# ATBR
########################################################################
project atbr 'https://github.com/coq-community/atbr' '5e3f4fe63d6423f672e03f15052068fe2fd5a3fc'
# Contact @palmskog, @tchajed on github

########################################################################
# perennial
########################################################################
project perennial 'https://github.com/mit-pdos/perennial' '43507a79689a8745477e6662d4dfb46d4cb64c73'
# Contact @upamanyus, @RalfJung, @tchajed on github
# PRs to fix Perennial failures should be submitted against the Perennial
# `master` branch. `coq/tested` is automatically updated every night to the
# `master` branch if CI on `master` is green. This is to avoid breaking Coq CI
# when Perennial CI breaks.

########################################################################
# metacoq
########################################################################
project metacoq 'https://github.com/MetaCoq/metacoq' 'b4d67e4dbd075fe3f0fdd5566cc56ab345afcfa6'
# Contact @mattam82, @yforster on github

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' '291e3b86b8c9ba22bf2edfaa183b3e7b03df7e95'
# Contact @bcpierce00, @liyishuai on github

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' 'a36352930b5e5f8d33dda09eef0c9d7c96190a02'
# Contact @whonore on github

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' '5712f82f94d00c2229fbb8cb144bac495d03e7ab'
# Contact @arthuraa on github

########################################################################
# VsCoq
########################################################################
project vscoq 'https://github.com/coq-community/vscoq' '8cdb3e6a8e74fd345e546d4d155bf172521af0f5'
# Contact @rtetley, @gares on github

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' 'f8295f0d77ab0dd9f989e8e45d43670a69f424df'
# Contact @jwiegley on github

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' '782ec4f7b29f8a925ff7a4c72dab727c6bd656ed'
# Contact @fajb on github

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word "https://github.com/jasmin-lang/coqword" "v2.2"
# Contact @vbgl, @strub on github
# go back to "main" and change dependency to MC 2 when
# https://github.com/jasmin-lang/jasmin/pull/560 is merged

########################################################################
# Jasmin
########################################################################
project jasmin "https://github.com/jasmin-lang/jasmin" "e8380c779b5c284c6d4c654d4ea86c56521a6d4c"
# Contact @vbgl, @bgregoir on github
# go back to "main" and change dependency to MC 2 when
# https://github.com/jasmin-lang/jasmin/pull/560 is merged

########################################################################
# Lean Importer
########################################################################
project lean_importer 'https://github.com/SkySkimmer/coq-lean-import' 'ce8ed08172d3247d992dacab08e0e8f59864a57b'
# Contact @SkySkimmer on github

########################################################################
# SerAPI
########################################################################
project serapi 'https://github.com/ejgallego/coq-serapi' 'eb845aa47fca05b743478a7878c218503c1cc0c7'
# Contact @ejgallego on github

########################################################################
# SMTCoq
########################################################################
project smtcoq 'https://github.com/smtcoq/smtcoq' 'd951f13947d75c6e52c56523fd3cfcc7c8911b2b'
# Contact @ckeller on github

########################################################################
# Stalmarck
########################################################################
project stalmarck 'https://github.com/coq-community/stalmarck' 'd32acd3c477c57b48dd92bdd96d53fb8fa628512'
# Contact @palmskog on github

########################################################################
# coq-library-undecidability
########################################################################
project coq_library_undecidability 'https://github.com/uds-psl/coq-library-undecidability' '40d38b1f94712322b12610418e1a02a7e3772977'
# Contact @mrhaandi, @yforster on github

########################################################################
# Tactician
########################################################################
project tactician 'https://github.com/coq-tactician/coq-tactician' '4a788f26ad8c8b0c02dad2b41b80cf331a4b64fc'
# Contact @LasseBlaauwbroek on github

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler 'https://github.com/SkySkimmer/coq-ltac2-compiler' '30ee5bbf04ab841deb3481465ef4753f2c69338e'
# Contact @SkySkimmer on github

########################################################################
# Waterproof
########################################################################
project waterproof 'https://github.com/impermeable/coq-waterproof' 'fb0bd1d8b4007f362acf5e7ce1d1b844b4f83d77'
# Contact @jellooo038, @jim-portegies on github

########################################################################
# Autosubst (2) OCaml
########################################################################
project autosubst_ocaml 'https://github.com/uds-psl/autosubst-ocaml' '830b3d6c561fa9227fc83738b4d02e8da9f68bab'
# Contact @yforster on github

########################################################################
# Trakt
########################################################################
project trakt 'https://github.com/ecranceMERCE/trakt' 'f9bb47018b3368b79b9d91fffdfe400762bc3010'
# Contact @ckeller, @louiseddp on github
