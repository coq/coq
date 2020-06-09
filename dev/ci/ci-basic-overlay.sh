#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
: "${mathcomp_CI_REF:=3515b33b1245ea169fbaf61405dc60954509fee2}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"
: "${mathcomp_CI_ARCHIVEURL:=${mathcomp_CI_GITURL}/archive}"

: "${fourcolor_CI_REF:=8d21f623b70a996c8b0ccf73c7995db46ac60d68}"
: "${fourcolor_CI_GITURL:=https://github.com/math-comp/fourcolor}"
: "${fourcolor_CI_ARCHIVEURL:=${fourcolor_CI_GITURL}/archive}"

: "${oddorder_CI_REF:=ddbaa599b461b99c53dd7ba08d0300d14e11f796}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order}"
: "${oddorder_CI_ARCHIVEURL:=${oddorder_CI_GITURL}/archive}"

########################################################################
# UniMath
########################################################################
: "${unimath_CI_REF:=2aec9849a4593df6fb40e598e04400721b3bfa62}"
: "${unimath_CI_GITURL:=https://github.com/UniMath/UniMath}"
: "${unimath_CI_ARCHIVEURL:=${unimath_CI_GITURL}/archive}"

########################################################################
# Unicoq + Mtac2
########################################################################
: "${unicoq_CI_REF:=68ed13294ea8860a8c39950f7ca2ff0aa7211b9f}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

: "${mtac2_CI_REF:=62071fe76d05e7d1bd43583514ad498102b556bd}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2}"
: "${mtac2_CI_ARCHIVEURL:=${mtac2_CI_GITURL}/archive}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_REF:=76dd3ec890ca0b6520a054763f62a7c6829f4ff6}"
: "${math_classes_CI_GITURL:=https://github.com/coq-community/math-classes}"
: "${math_classes_CI_ARCHIVEURL:=${math_classes_CI_GITURL}/archive}"

: "${corn_CI_REF:=6f419847423b3640b558ccf6bc3cecf87fdf1b16}"
: "${corn_CI_GITURL:=https://github.com/coq-community/corn}"
: "${corn_CI_ARCHIVEURL:=${corn_CI_GITURL}/archive}"

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/iris/stdpp}"
: "${stdpp_CI_ARCHIVEURL:=${stdpp_CI_GITURL}/-/archive}"

: "${iris_CI_GITURL:=https://gitlab.mpi-sws.org/iris/iris}"
: "${iris_CI_ARCHIVEURL:=${iris_CI_GITURL}/-/archive}"

: "${lambda_rust_CI_REF:=9418275e0cc22f7bfc840a94e0e64b175268225f}"
: "${lambda_rust_CI_GITURL:=https://gitlab.mpi-sws.org/iris/lambda-rust}"
: "${lambda_rust_CI_ARCHIVEURL:=${lambda_rust_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
: "${hott_CI_REF:=fe02e95f60d8dae5b3a15840c3625c64b5f96eaf}"
: "${hott_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${hott_CI_ARCHIVEURL:=${hott_CI_GITURL}/archive}"

########################################################################
# CoqHammer
########################################################################
: "${coqhammer_CI_REF:=39184be71da29710e7486360d178f2e1a7a93c00}"
: "${coqhammer_CI_GITURL:=https://github.com/lukaszcz/coqhammer}"
: "${coqhammer_CI_ARCHIVEURL:=${coqhammer_CI_GITURL}/archive}"

########################################################################
# GeoCoq
########################################################################
: "${geocoq_CI_REF:=8c06688b54dd56249785f74203c3b38208c9a30a}"
: "${geocoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"
: "${geocoq_CI_ARCHIVEURL:=${geocoq_CI_GITURL}/archive}"

########################################################################
# Flocq
########################################################################
: "${flocq_CI_REF:=db11908f26581a366d791b03c50b3ea74791f193}"
: "${flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"
: "${flocq_CI_ARCHIVEURL:=${flocq_CI_GITURL}/-/archive}"

########################################################################
# coq-tools
########################################################################
: "${coq_tools_CI_REF:=de6a82141c41342a2abcbc9c0402a98393bcff35}"
: "${coq_tools_CI_GITURL:=https://github.com/JasonGross/coq-tools}"
: "${coq_tools_CI_ARCHIVEURL:=${coq_tools_CI_GITURL}/archive}"

########################################################################
# Coquelicot
########################################################################
: "${coquelicot_CI_REF:=4b000e5220d7b30ebc323564c10c60f6e2d22733}"
: "${coquelicot_CI_GITURL:=https://gitlab.inria.fr/coquelicot/coquelicot}"
: "${coquelicot_CI_ARCHIVEURL:=${coquelicot_CI_GITURL}/-/archive}"

########################################################################
# Coq-interval
########################################################################
: "${interval_CI_REF:=540621b251bff27698b321375568a05726a86991}"
: "${interval_CI_GITURL:=https://gitlab.inria.fr/coqinterval/interval}"
: "${interval_CI_ARCHIVEURL:=${interval_CI_GITURL}/-/archive}"

########################################################################
# Gappa stand alone tool
########################################################################
: "${gappa_tool_CI_REF:=f53e105cd73484fc76eb58ba24ead73be502c608}"
: "${gappa_tool_CI_GITURL:=https://gitlab.inria.fr/gappa/gappa}"
: "${gappa_tool_CI_ARCHIVEURL:=${gappa_tool_CI_GITURL}/-/archive}"

########################################################################
# Gappa plugin
########################################################################
: "${gappa_plugin_CI_REF:=494fb283b2fba166aa1c108715e9820c5adabac1}"
: "${gappa_plugin_CI_GITURL:=https://gitlab.inria.fr/gappa/coq}"
: "${gappa_plugin_CI_ARCHIVEURL:=${gappa_plugin_CI_GITURL}/-/archive}"

########################################################################
# CompCert
########################################################################
# This uses the platform supplied version of Flocq and Menhirlib as
# published in http://coq.io/opam/coq-compcert.3.7~coq-platform.html
# with a few additional patches for 8.12
# Author codes:
# SN : Michael Soegtrop, new (not in the above opam release)
# SO : Michael Soegtrop, opam (in the above opam release)
# CN : CompCert GIT, new (not in the above opam release)
# CO : CompCert GIT, opam (in the above opam release)
# 172f55fd SN Don't build MenhirLib (platform version is used)
# 1feb12c8 SO Use platform supplied menhirlib as suggested by jhjourdan
# 6a8204d4 SN Use ocamlfind to find menhirLib
# e2c86f5a CN Coq-MenhirLib: explicit import ListNotations (#354)
# 48d9cbd2 CN Import ListNotations explicitly
# 4accc3dd SO Use Coq platform supplied Flocq
# 16878a61 CO Update the list of dual-licensed files
# cea50ef9 CO Dual-license aarch64/{Archi.v,Cbuiltins.ml,extractionMachdep.v}
# b7980c83 CO Install "compcert.config" file along the Coq development
# 76a4ff8f    Updates for release 3.7
: "${compcert_platform_CI_REF:=coq-platform-8.12.beta}"
: "${compcert_platform_CI_GITURL:=https://github.com/MSoegtropIMC/CompCert}"
: "${compcert_platform_CI_ARCHIVEURL:=${compcert_platform_CI_GITURL}/archive}"

# As above, but does use bundled Flocq and Menhirlib rather than the
# platform supplied version
# This is used by the Windows Installer (and the Coq platform)
# 10bafbaa CN Coq-MenhirLib: explicit import ListNotations (#354)
# f494c983 CN Import ListNotations explicitly
# 16878a61 CO Update the list of dual-licensed files
# cea50ef9 CO Dual-license aarch64/{Archi.v,Cbuiltins.ml,extractionMachdep.v}
# b7980c83 CO Install "compcert.config" file along the Coq development
# 76a4ff8f    Updates for release 3.7
: "${compcert_CI_REF:=coq-8.12.beta}"
: "${compcert_CI_GITURL:=https://github.com/MSoegtropIMC/CompCert}"
: "${compcert_CI_ARCHIVEURL:=${compcert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
# This commit sets the version number to 2.6
# M.Soegtrop discussed with A.Appel via email to use this commit for 8.12.beta
: "${vst_CI_REF:=766971b60f705e7e8b890e533518bdc79a9a60b5}"
: "${vst_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${vst_CI_ARCHIVEURL:=${vst_CI_GITURL}/archive}"

# This is a paltform friendly variant using paltform supplied compcert and Flocq
# This is used by the Windows Installer (and the Coq platform)
# This includes one extra commit relative to the above:
# 45239bb5 MSoegtrop Changed build and CI system to use opam / coq-platform supplied CompCert
: "${vst_platform_CI_REF:=coq-platform-8.12.beta}"
: "${vst_platform_CI_GITURL:=https://github.com/MSoegtropIMC/VST}"
: "${vst_platform_CI_ARCHIVEURL:=${vst_platform_CI_GITURL}/archive}"

########################################################################
# cross-crypto
########################################################################
: "${cross_crypto_CI_REF:=62e64fdbcbdaddde77a62d92e9adc15fa6562d2a}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto}"
: "${cross_crypto_CI_ARCHIVEURL:=${cross_crypto_CI_GITURL}/archive}"

########################################################################
# rewriter
########################################################################
: "${rewriter_CI_REF:=818069e0e5c46fc365466b7cd83a183a81a0e99a}"
: "${rewriter_CI_GITURL:=https://github.com/mit-plv/rewriter}"
: "${rewriter_CI_ARCHIVEURL:=${rewriter_CI_GITURL}/archive}"

########################################################################
# fiat_parsers
########################################################################
: "${fiat_parsers_CI_REF:=0b1ebaa1eb779bcbe91aeef38a4364a33bce800f}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat}"
: "${fiat_parsers_CI_ARCHIVEURL:=${fiat_parsers_CI_GITURL}/archive}"

########################################################################
# fiat_crypto
########################################################################
: "${fiat_crypto_CI_REF:=a841138d470f6f44c4e4afe8e18c0b56bb3a7b27}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_CI_ARCHIVEURL:=${fiat_crypto_CI_GITURL}/archive}"

########################################################################
# coq_dpdgraph
########################################################################
: "${coq_dpdgraph_CI_REF:=acd7c15cf6ca33c00f39092716936c2d0c0e40dc}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"
: "${coq_dpdgraph_CI_ARCHIVEURL:=${coq_dpdgraph_CI_GITURL}/archive}"

########################################################################
# CoLoR
########################################################################
: "${color_CI_REF:=1f1cd5e05bc193d121e78091a5817213ddbe41af}"
: "${color_CI_GITURL:=https://github.com/fblanqui/color}"
: "${color_CI_ARCHIVEURL:=${color_CI_GITURL}/archive}"

########################################################################
# TLC
########################################################################
: "${tlc_CI_REF:=0cf2a7f95f09ffe54854bc29dd93869dc2fd091e}"
: "${tlc_CI_GITURL:=https://github.com/charguer/tlc}"
: "${tlc_CI_ARCHIVEURL:=${tlc_CI_GITURL}/archive}"

########################################################################
# Bignums
########################################################################
: "${bignums_CI_REF:=657e8d07f7bf26a55b51456cf26332dfea730bc2}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"
: "${bignums_CI_ARCHIVEURL:=${bignums_CI_GITURL}/archive}"

########################################################################
# coqprime
########################################################################
: "${coqprime_CI_REF:=cd1cbb7c1df83ae8f6840ef549028c50a1f1f87f}"
: "${coqprime_CI_GITURL:=https://github.com/thery/coqprime}"
: "${coqprime_CI_ARCHIVEURL:=${coqprime_CI_GITURL}/archive}"

########################################################################
# bbv
########################################################################
: "${bbv_CI_REF:=9ee6027ceb931700ad19c09da7830b47c004743f}"
: "${bbv_CI_GITURL:=https://github.com/mit-plv/bbv}"
: "${bbv_CI_ARCHIVEURL:=${bbv_CI_GITURL}/archive}"

########################################################################
# bedrock2
########################################################################
: "${bedrock2_CI_REF:=484a6916eb454778c82a5f6830051dd7cf91b1b6}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"
: "${bedrock2_CI_ARCHIVEURL:=${bedrock2_CI_GITURL}/archive}"

########################################################################
# Equations
########################################################################
: "${equations_CI_REF:=74f048116242d7fb13cbc554522f02fe270720d2}"
: "${equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${equations_CI_ARCHIVEURL:=${equations_CI_GITURL}/archive}"

########################################################################
# Elpi + Hierarchy Builder
########################################################################
: "${elpi_CI_REF:=75b82ca6826270a5d399250fd5862da7aa9c9fdd}"
: "${elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${elpi_CI_ARCHIVEURL:=${elpi_CI_GITURL}/archive}"

: "${elpi_hb_CI_REF:=7852848fe5587d27c419871ea22dd91f96b51ab2}"
: "${elpi_hb_CI_GITURL:=https://github.com/math-comp/hierarchy-builder}"
: "${elpi_hb_CI_ARCHIVEURL:=${elpi_hb_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_REF:=ad124361042d49612b110984a8f3bb16bbec871e}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# ext-lib
########################################################################
: "${ext_lib_CI_REF:=ac5f1df273b98f53ba2573cfffcbbbf1e388e4d2}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-community/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
: "${simple_io_CI_REF:=2901321752c2184febe5224d5bfd74295a030e72}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################
: "${quickchick_CI_REF:=2d430e638124af66a343bec51243d1adc182a8cf}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
: "${quickchick_CI_ARCHIVEURL:=${quickchick_CI_GITURL}/archive}"

########################################################################
# reduction-effects
########################################################################
: "${reduction_effects_CI_REF:=1f1a977b8399122e16f9c1f640bcb31573773cbf}"
: "${reduction_effects_CI_GITURL:=https://github.com/coq-community/reduction-effects}"
: "${reduction_effects_CI_ARCHIVEURL:=${reduction_effects_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################

# Note: menhirlib is now in subfloder coq-menhirlib of menhir
: "${menhirlib_CI_REF:=20200525}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/menhir}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac_tactics
########################################################################
: "${aac_tactics_CI_REF:=2db18d6483fe473de83d59373535ad56c02f7640}"
: "${aac_tactics_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aac_tactics_CI_ARCHIVEURL:=${aac_tactics_CI_GITURL}/archive}"

########################################################################
# paramcoq
########################################################################
: "${paramcoq_CI_REF:=aa2f620e75a6fabe6af654a61b3959902df2d69e}"
: "${paramcoq_CI_GITURL:=https://github.com/coq-community/paramcoq}"
: "${paramcoq_CI_ARCHIVEURL:=${paramcoq_CI_GITURL}/archive}"

########################################################################
# relation_algebra
########################################################################
: "${relation_algebra_CI_REF:=c3c669003d9b3f1d0b2f97a197f81b8efd80f5b7}"
: "${relation_algebra_CI_GITURL:=https://github.com/damien-pous/relation-algebra}"
: "${relation_algebra_CI_ARCHIVEURL:=${relation_algebra_CI_GITURL}/archive}"

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
: "${struct_tact_CI_REF:=2e5fc017d51edfe2d15950e73b5b028ecb5d330b}"
: "${struct_tact_CI_GITURL:=https://github.com/uwplse/StructTact}"
: "${struct_tact_CI_ARCHIVEURL:=${struct_tact_CI_GITURL}/archive}"

: "${inf_seq_ext_CI_REF:=203d4c20211d6b17741f1fdca46dbc091f5e961a}"
: "${inf_seq_ext_CI_GITURL:=https://github.com/DistributedComponents/InfSeqExt}"
: "${inf_seq_ext_CI_ARCHIVEURL:=${inf_seq_ext_CI_GITURL}/archive}"

: "${cheerios_CI_REF:=9c7f66e57b91f706d70afa8ed99d64ed98ab367d}"
: "${cheerios_CI_GITURL:=https://github.com/uwplse/cheerios}"
: "${cheerios_CI_ARCHIVEURL:=${cheerios_CI_GITURL}/archive}"

: "${verdi_CI_REF:=fdb4ede19d2150c254f0ebcfbed4fb9547a734b0}"
: "${verdi_CI_GITURL:=https://github.com/uwplse/verdi}"
: "${verdi_CI_ARCHIVEURL:=${verdi_CI_GITURL}/archive}"

: "${verdi_raft_CI_REF:=bae738350f4b23b70d7489e89b6e186cd187484e}"
: "${verdi_raft_CI_GITURL:=https://github.com/uwplse/verdi-raft}"
: "${verdi_raft_CI_ARCHIVEURL:=${verdi_raft_CI_GITURL}/archive}"

########################################################################
# stdlib2
########################################################################
: "${stdlib2_CI_REF:=61fdb3649e00c4b713614f165161011ae545aacf}"
: "${stdlib2_CI_GITURL:=https://github.com/coq/stdlib2}"
: "${stdlib2_CI_ARCHIVEURL:=${stdlib2_CI_GITURL}/archive}"

########################################################################
# argosy
########################################################################
: "${argosy_CI_REF:=016c8f89c714604d01db43be2687c9cac7b3a4b6}"
: "${argosy_CI_GITURL:=https://github.com/mit-pdos/argosy}"
: "${argosy_CI_ARCHIVEURL:=${argosy_CI_GITURL}/archive}"

########################################################################
# perennial
########################################################################
: "${perennial_CI_REF:=60aadeb94ad8f5a8f5ac7d9a0a123cc344307f3f}"
: "${perennial_CI_GITURL:=https://github.com/mit-pdos/perennial}"
: "${perennial_CI_ARCHIVEURL:=${perennial_CI_GITURL}/archive}"

########################################################################
# metacoq
########################################################################
: "${metacoq_CI_REF:=4e6d6df053b772e627dab8dd00627bd37830787a}"
: "${metacoq_CI_GITURL:=https://github.com/MetaCoq/metacoq}"
: "${metacoq_CI_ARCHIVEURL:=${metacoq_CI_GITURL}/archive}"

########################################################################
# SF suite
########################################################################
: "${sf_CI_REF:=d41a56ee075259f271ae5288f7860b340cabc3a1}"
: "${sf_CI_GITURL:=https://github.com/DeepSpec/sf}"
: "${sf_CI_ARCHIVEURL:=${sf_CI_GITURL}/archive}"
