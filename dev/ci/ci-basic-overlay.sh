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
project mathcomp 'https://github.com/math-comp/math-comp' '21781acfe13bce43aa4b53126c3463ce4a282ca9'
# Contact @CohenCyril, @proux01 on github

project fourcolor 'https://github.com/math-comp/fourcolor' '1739214a760d7844e971cb8170707b0395f55c6d'
# Contact @ybertot, @proux01 on github

project oddorder 'https://github.com/math-comp/odd-order' '2bee03dd95d4282f0c13d2eec748a2dcf92fc473'
# Contact @gares, @proux01 on github

project mczify 'https://github.com/math-comp/mczify' '0d2b9fd068f6477b3d8ef53b302e6f2719f71d78'
# Contact @pi8027 on github

project finmap 'https://github.com/math-comp/finmap' 'a2f06d1f0bb05afce1f5a9bb73b6398e521bf3a9'
# Contact @CohenCyril on github

project bigenough 'https://github.com/math-comp/bigenough' '5a5ff278089847d31a28067eb7ca4fad6a49f11c'
# Contact @CohenCyril on github

project analysis 'https://github.com/math-comp/analysis' '3cff9bb331cb0d72bce95bed8e279f93b6d5e23a'
# Contact @affeldt-aist, @CohenCyril on github

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '0f7bb63aae9fb6179d653d6c39cb1e8e72f2c789'
# Contact @benediktahrens, @m-lindgren, @nmvdw, @rmatthes on github

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' 'a9b72f755539c0b3280e38e778a09e2b7519a51a'
# Contact @beta-ziliani, @Janno, @mattam82 on github

project mtac2 'https://github.com/Mtac2/Mtac2' '1cdb2cb628444ffe9abc6535f6d2e11004de7fc1'
# Contact @beta-ziliani, @Janno, @mattam82 on github

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' '9db314291e4db1fd30bb0ef21292c78920298a6e'
# Contact @Lysxia and @spitters on github

project corn 'https://github.com/coq-community/corn' 'a75b14fad50313d615881713d4703e6c9cd6e111'
# Contact @Lysxia and @spitters on github

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

project autosubst 'https://github.com/coq-community/autosubst' '50dfe574c0bd415925eea47c1f5b1a533aa85269'
# Contact @RalfJung, @co-dan on github

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' '4f54a3254f47e2d65f92e20a56b97cc2098ac00b'
# Contact @RalfJung, @robbertkrebbers on github

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' 'bb95699e33b1a496d7d31e418c0cb837b2acbaa3'
# Contact @Alizter, @jdchristensen on github

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '31442e8178a5d85a9f57a323b65bf9f719ded8ec'
# Contact @lukaszcz on github

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '0a685a5c8b86f992e74a3e675acf882afacf2de6'
# Contact @silene on github

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' '0e14c7b4475d5ea7c3a6aa416f4a761b0e9f8b2f'
# Contact @JasonGross on github

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' 'f513668494d3fb9541cee98625ed8488678048a7'
# Contact @JasonGross on github

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' '88672c1eac54f78ee733c42c0bdb2ac9905aad1e'
# Contact @silene on github

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' '54341fe9728ca74fb446145c327220af33f8a701'
# Contact @xavierleroy on github

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' '21f3ac51a1e53ec74d5926a55c5ef9d4d62fda51'
# Contact @andrew-appel on github

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' '433e91211a333e73566b0eaa4da1a7d12ed972aa'
# Contact @andres-erbsen on github

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' '30c8507c1e30626b2aa1e15c0aa7c23913da033c'
# Contact @JasonGross on github

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' '41a0b8dd92a252fcf7491ee99e16eb002288e87e'
# Contact @JasonGross on github

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '9e79fa6d3e8427c4f75321dbd426c86c483891c1'
# Contact @JasonGross on github

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' 'eedc9c86c55487cfcf7b40234e8780b8bd8b24db'
# Contact @andres-erbsen, @JasonGross on github

# bedrock2, coqutil, rupicola, kami, riscv_coq
# fiat-crypto is not guaranteed to build with the latest version of
# bedrock2, so we use the pinned version of bedrock2 for fiat-crypto
# overlays do not have to follow suite
subproject rupicola fiat_crypto "rupicola" "https://github.com/mit-plv/rupicola" "master"
subproject bedrock2 rupicola "bedrock2" "https://github.com/mit-plv/bedrock2" "master"
subproject coqutil bedrock2 "deps/coqutil" "https://github.com/mit-plv/coqutil" "master"
subproject kami bedrock2 "deps/kami" "https://github.com/mit-plv/kami" "rv32i"
subproject riscv_coq bedrock2 "deps/riscv-coq" "https://github.com/mit-plv/riscv-coq" "master"
# Contact @samuelgruetter, @andres-erbsen on github

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/coq-community/coq-dpdgraph' '74ced1b11a8df8d4c04c3829fcf273aa63d2c493'
# Contact @Karmaki, @ybertot on github

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' 'c867546cea21f74aad86e0a34ceaf93ed9259f96'
# Contact @fblanqui on github

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' '51be762eedec72788490f1fd222eb8b0d82b8bea'
# Contact @charguer on github

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' 'cc2d9ee990e4cfebe5f107d8357198baa526eded'
# Contact @erikmd, @proux01 on github

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' '845c00cadc521aa70c3a8ae3bef9e2fabcbabf19'
# Contact @thery on github

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' 'c53d5b95c70839ae8e947010d85503bd1ada1120'
# Contact @JasonGross, @samuelgruetter on github

########################################################################
# Coinduction
########################################################################
project coinduction 'https://github.com/damien-pous/coinduction' '09caaf1f809e3e91ebba05bc38cef6de83ede3b3'
# Contact @damien-pous on github

########################################################################
# coq-lsp
########################################################################
project coq_lsp 'https://github.com/ejgallego/coq-lsp' '25d8b8672beaa39bafa1f91d62910cad49c381f9'
# Contact @ejgallego on github

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' '3431c88a7575a3972191c25809c563aafdc6414e'
# Contact @mattam82 on github

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' '185416f6e157e1a2b0502dc8a3880fd02a6a2358'
# Contact @gares on github

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' 'be3bc5943053d5186e8933b510e663ac40a25f6b'
# Contact @CohenCyril, @gares on github

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' '08ecd3ae6e73ff6e62b47fd62f5c57e4ec4fb42d'
# Contact @JasonGross on github

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' '2da486d949709643ca54026a6a24d5ee36baafc0'
# Contact @aleksnanevski, @clayrat on github

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' 'b27e806daf39a8f1cfc7ced09c1af44d390af4a6'
# Contact @gmalecha, @liyishuai on github

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' '59ca9ed99f7e178e40a32e3ea513dfe9be3a12aa'
# Contact @Lysxia, @liyishuai on github

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' '7b33d19066aa762629cbbe210d41067f56dce000'
# Contact @lemonidas, @Lysxia, @liyishuai on github

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' '2e6590125885906ec0c5157b114d2afba18ab9c8'
# Contact @liyishuai, @JasonGross on github

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib 'https://gitlab.inria.fr/fpottier/menhir' '809af6503305acaf6d9877e67c40ef651452e115'
# Contact @fpottier, @jhjourdan on github

########################################################################
# coq-neural-net-interp
########################################################################
project neural_net_interp 'https://github.com/JasonGross/neural-net-coq-interp' '1a3d72129fa5e6f05e093e9e19e94f2110c73d0f'
# Contact @JasonGross on github

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' '109af844f39bf541823271e45e42e40069f3c2c4'
# Contact @palmskog on github

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' '5efd5da088e26bf4351e3abd258f8a3f848fe00c'
# Contact @minkiminki on github

########################################################################
# coq-itree
########################################################################
project itree 'https://github.com/DeepSpec/InteractionTrees' '1e8bc121ec8e8d6f699f0231bb7f92ebfd54f4b9'
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
project parsec 'https://github.com/liyishuai/coq-parsec' '3feabc998705927ca2d2f9249a21a6e15c394162'
# Contact @liyishuai on github

########################################################################
# coq-json
########################################################################
project json 'https://github.com/liyishuai/coq-json' '8069b6b4d544ea3011246dfa04d2c1c550d50455'
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
project paramcoq 'https://github.com/coq-community/paramcoq' '32609ca4a9bf4a0e456a855ea5118d8c00cda6be'
# Contact @proux01 on github

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' '7966d1a7bb524444120c56c3474717bcc91a5215'
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
# Stdlib
########################################################################
project stdlib 'https://github.com/coq/stdlib' 'V9.0.0'
# Contact TODO on github

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' '9fa42b78b7f9b7b989fb3434dfbfec4abcfcbff8'
# Contact @tchajed on github

########################################################################
# ATBR
########################################################################
project atbr 'https://github.com/coq-community/atbr' '47ac8fb6bf244d9a4049e04c01e561191490f543'
# Contact @palmskog, @tchajed on github

########################################################################
# perennial
########################################################################
project perennial 'https://github.com/mit-pdos/perennial' '12aec9c9829939c32eb8eca85371d713d73293d9'
# Contact @upamanyus, @RalfJung, @tchajed on github
# PRs to fix Perennial failures should be submitted against the Perennial
# `master` branch. `coq/tested` is automatically updated every night to the
# `master` branch if CI on `master` is green. This is to avoid breaking Coq CI
# when Perennial CI breaks.

########################################################################
# metacoq
########################################################################
project metacoq 'https://github.com/MetaCoq/metacoq' '17ba45ffc84d37e187ef87a55b840890f1d87f01'
# Contact @mattam82, @yforster on github

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' '5e863a9f92e515a0e11641f28077a64919f8482e'
# Contact @bcpierce00, @liyishuai on github

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' '9bd2a1818e08fd6e52d72024a60c51a983770c81'
# Contact @whonore on github

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' '9dcb5de11b26afa8c14a137f164413a61612a53d'
# Contact @arthuraa on github

########################################################################
# VsCoq
########################################################################
project vscoq 'https://github.com/coq-community/vscoq' '36f5a395a28cb5d6c556daeae3b287295304d00e'
# Contact @rtetley, @gares on github

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' '255751fab5650c45095bbc2ac156ca9fcac17c9c'
# Contact @jwiegley on github

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' 'c13c6b4a0070ecc3ae8ea9755a1d6a163d123127'
# Contact @fajb on github

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word 'https://github.com/jasmin-lang/coqword' '1abe5ade5240115aed1e3c140e261f1554af2322'
# Contact @vbgl, @strub on github

########################################################################
# Jasmin
########################################################################
project jasmin 'https://github.com/jasmin-lang/jasmin' '41068bc89855cd0f015e78472e32fda9230e3218'
# Contact @vbgl, @bgregoir on github

########################################################################
# Lean Importer
########################################################################
project lean_importer 'https://github.com/SkySkimmer/coq-lean-import' 'c513cee4f5edf8e8a06ba553ca58de5142cffde6'
# Contact @SkySkimmer on github

########################################################################
# SMTCoq
########################################################################
project smtcoq 'https://github.com/smtcoq/smtcoq' '5c6033c906249fcf98a48b4112f6996053124514'
# Contact @ckeller on github

project smtcoq_trakt 'https://github.com/smtcoq/smtcoq' '9392f7446a174b770110445c155a07b183cdca3d'
# Contact @ckeller on github

########################################################################
# Stalmarck
########################################################################
project stalmarck 'https://github.com/coq-community/stalmarck' 'd32acd3c477c57b48dd92bdd96d53fb8fa628512'
# Contact @palmskog on github

########################################################################
# Tactician
########################################################################
project tactician 'https://github.com/coq-tactician/coq-tactician' '62efb022e34ce141306be9c646f4e2f3fe40c4b0'
# Contact @LasseBlaauwbroek on github

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler 'https://github.com/SkySkimmer/coq-ltac2-compiler' '30ee5bbf04ab841deb3481465ef4753f2c69338e'
# Contact @SkySkimmer on github

########################################################################
# Waterproof
########################################################################
project waterproof 'https://github.com/impermeable/coq-waterproof' '443f794ddc102309d00f1d512ab50b84fdc261aa'
# Contact @jellooo038, @jim-portegies on github

########################################################################
# Autosubst (2) OCaml
########################################################################
project autosubst_ocaml 'https://github.com/uds-psl/autosubst-ocaml' 'a4e154fb548197572326167809a4c612a2ec71ac'
# Contact @yforster on github

########################################################################
# Trakt
########################################################################
project trakt 'https://github.com/ecranceMERCE/trakt' '956e78ab3680d186d03d8b58dbd90681174f3157'
# Contact @ckeller, @louiseddp on github
