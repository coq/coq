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
project mathcomp 'https://github.com/math-comp/math-comp' '6fcb8c35e9bd7ed0d74d6870893b2d3a69cbe67c'

project fourcolor "https://github.com/math-comp/fourcolor" "e831b0b00e264285f91938917a0a5ef64ec1a829"
# put back master when testing MathComp 2
# project fourcolor "https://github.com/math-comp/fourcolor" "master"

project oddorder "https://github.com/math-comp/odd-order" "2c03794e64eef467442a4ea2ef1430b13b0faa97"
# put back master when testing MathComp 2
# project oddorder "https://github.com/math-comp/odd-order" "master"

project mczify "https://github.com/math-comp/mczify" "2046446984f7b8c8f5102df4df6076b60874e688"
# put back master when testing MathComp 2
# project mczify "https://github.com/math-comp/mczify" "master"

project finmap "https://github.com/math-comp/finmap" "cea9f088c9cddea1173bc2f7c4c7ebda35081b60"
# put back master when testing MathComp 2
# project finmap "https://github.com/math-comp/finmap" "master"

project bigenough 'https://github.com/math-comp/bigenough' 'ff71b25f31658d80fdae9657e8cf34e5e1052647'

project analysis "https://github.com/math-comp/analysis" "9193f4a1278409cc13a1de739adf3620aa24a638"
# put back master when testing MathComp 2
# project analysis "https://github.com/math-comp/analysis" "master"

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '18f15a8eb58f20680672b074354c1b1b82aec4dc'

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' 'd9b0e1f5b1b51f06a8e2f21910c3c117e9233d6a'

project mtac2 'https://github.com/Mtac2/Mtac2' '29dc0ae56db985ba3d052e59c84a7d67471d6e8f'

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' '7a57556e489989cb38899decf61ea66f4394c60f'

project corn 'https://github.com/coq-community/corn' 'c08a0418f97a04ea7a6cdc3a930561cc8fc84d82'

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""

project iris "https://gitlab.mpi-sws.org/iris/iris" ""

project autosubst 'https://github.com/coq-community/autosubst' '495d547fa2a3e40da0f7d2a31469ac8caab058d2'

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' 'f899efbd7c49ed4ead30ac67b1595602f0b091ec'

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' '832aef3e6fff0f5b953ed170522e1a3d6288a4bb'

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '35b1ddb346ff4739d4b7d0aaa2ee34ebb1de22ae'

########################################################################
# GeoCoq
########################################################################
project geocoq 'https://github.com/GeoCoq/GeoCoq' 'b0f922bdf06bc175155a0a489a451fb73c1e403a'

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '2c499dc6fd577ee13ac84ee6a0bad5024055aa29'

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' '4aaef74e5742fe3ad87c5d18d735e82b1284ecc6'

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' '7562bafc9b21cb34d74f869632455e67d11f5bc3'

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' 'df29052d3607adaf9c7d1e663a13c36149035e8f'

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' '222bd6d812b726be939eb8afc67b935a08799bfa'

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' 'cd6f85a813069ab7742d3f6e1510960230a86e2e'

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' '964dc89064da3232ffb202474bf9b775c581ee5c'

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' 'c79bbc9148fb8386e188267c684a882d8634293b'

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' '2bb593d87a7005cca74dd5e6810d311f2872b4b4'

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' 'c371fb8945cf311aefc598bd7ae3ef0d4123b91e'

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '20ad035d5212531f5efb82f9fff32f26b80c39e6'

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/Karmaki/coq-dpdgraph' '8b4291573cc12a03d7e703e00dd82e5e80e5d446'

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' 'f2ef98f7d13c5d71dd2a614ed2e6721703a34532'

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' '198142f9db4427063c381450ad6a25839d7fd35c'

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' 'a8c50a569a971d6e36e8df88ca16f9f8958f9543'

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' '431d7a66877cbe8688fc8864ef892369401440e1'

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' '6144e214583b72182a4ed89e4328ea62ba766e2e'

########################################################################
# bedrock2
########################################################################
project bedrock2 'https://github.com/mit-plv/bedrock2' '0893c1f7d9ac2ef60c9b62cbbf54ec797d98728b'

########################################################################
# coq-lsp
########################################################################
project coq_lsp 'https://github.com/ejgallego/coq-lsp' 'f21555ee3903bd9a2ac1c70b5f7adbb0b5f38425'

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' '21a3306a7e13b3037d20492bfdb5da75463929fb'

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' 'd39c6ca16ac987490eedefdcddd09ca25202e862'

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' 'c8e542e7994f033151a47e77306e2a52929c9a2c'

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' '8c0b15abc38b1d3f7dc606f4eeef9fba1a986b05'

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' '35cb0a2235adb656c2696e33512f0c4555ad753b'

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' '995151f6df3768625922c3b2be5d9f4801b3dd3f'

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' '403db47e0b96222cd3c89c48ed5f8da10319da77'

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' '6cf6918a5add0e10512f4529719f8fd8a4b605fa'

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' '604528fa0e8472cd1d1264782ffcbfecb8571b48'

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib "https://gitlab.inria.fr/fpottier/menhir" "20220210"

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' '0f2de225cb6d42d93c8aa61891510e5c6ac6726c'

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' '5c5693f46c8957f36a2349a0d906e911366136de'

########################################################################
# coq-itree
########################################################################
project itree 'https://github.com/DeepSpec/InteractionTrees' 'eede8c539985e358e7149ab77b5c058def37571d'

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' '9d7f66fffbaf44e034f35c4ada50dac14824fe0b'

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' '1c37f34e53a0a0c523fbd813f9ae10e18f6e41f2'

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact 'https://github.com/uwplse/StructTact' '2f2ff253be29bb09f36cab96d036419b18a95b00'

project inf_seq_ext 'https://github.com/DistributedComponents/InfSeqExt' '601e89ec019501c48c27fcfc14b9a3c70456e408'

project cheerios 'https://github.com/uwplse/cheerios' 'bad8ad2476e14df6b5a819b7aaddc27a7c53fb69'

project verdi 'https://github.com/uwplse/verdi' '76833a7b2188e99e358b8439ea6b4f38401c962a'

project verdi_raft 'https://github.com/uwplse/verdi-raft' '7c8e4d53d27f7264ec4d3de72944dc0368e065f0'

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
project perennial 'https://github.com/mit-pdos/perennial' '42d4197a1990b27c9f9abc533a5cde9f5813115b'

########################################################################
# metacoq
########################################################################
project metacoq 'https://github.com/MetaCoq/metacoq' 'b34d3f32a8d73e4fea721df2cddb6be42509b3f0'

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' 'd98b8968483d7ee30dc3a502cd7d58f1490bfa9b'

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' 'ec80f3d48dcbf19209ef51d6020838cda5a1d46e'

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' 'bf967106a0b61a281c3b4ababfe67f80de7fba47'

########################################################################
# VsCoq
########################################################################
project vscoq 'https://github.com/coq-community/vscoq' 'ed40eda53d69dd17c14dce1542c83ddc81cab3e9'

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' '5376e32a4eeace4a84674820083bc2985a2a593f'

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' '04b02439e1a7383e8834caacb1a5031d873c1de4'

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word 'https://github.com/jasmin-lang/coqword' 'cb8b06aa14ab13b07e04011ae376b3a133cc911d'

########################################################################
# Jasmin
########################################################################
project jasmin 'https://github.com/jasmin-lang/jasmin' 'c8f25be1829036d23d486a8e9210f990a9a0c298'

########################################################################
# Lean Importer
########################################################################
project lean_importer 'https://github.com/SkySkimmer/coq-lean-import' 'c7dd746178afe675463a32d6550fed29fb011640'

########################################################################
# SerAPI
########################################################################
project serapi 'https://github.com/ejgallego/coq-serapi' '70ddb488161ae3447c91d811192101ac3cf97abb'

########################################################################
# SMTCoq
########################################################################
project smtcoq 'https://github.com/smtcoq/smtcoq' '4a29a8cdb77ec38a77e42c2dd3ef366ecda8834e'

########################################################################
# Stalmarck
########################################################################
project stalmarck 'https://github.com/coq-community/stalmarck' '9e6cd57df21f991ca5cdd54800707b96fba16ced'

########################################################################
# coq-library-undecidability
########################################################################
project coq_library_undecidability 'https://github.com/uds-psl/coq-library-undecidability' '0e29426de0e6749b851514968f3982db2e9e8ccb'

########################################################################
# Tactician
########################################################################
project tactician 'https://github.com/coq-tactician/coq-tactician' 'd01f50ae2e9eff55e10c6c2e6ce61df9970f04b6'

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler 'https://github.com/SkySkimmer/coq-ltac2-compiler' '064771bd53e1fd8f61fd27ae16ab84f262d37177'
