#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
# Latest tag on the math-comp repository.  This is a pre-release:
# should probably be updated for the 8.12.0 release.
: "${mathcomp_CI_REF:=mathcomp-1.11+beta1}"
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
# This is the last commit on master and the only one that is
# compatible with 8.12.  There was no branch nor any tag compatible
# with 8.11 either.
: "${unicoq_CI_REF:=68ed13294ea8860a8c39950f7ca2ff0aa7211b9f}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

# There's no 8.12-compatible release yet but there is an
# 8.12-compatible branch.
: "${mtac2_CI_REF:=master-8.12}"
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
# The latest release (from today) is compatible with Coq 8.12.
: "${flocq_CI_REF:=flocq-3.3.1}"
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
# The latest release (from 3 months ago) is compatible with Coq 8.12.
: "${coquelicot_CI_REF:=coquelicot-3.1.0}"
: "${coquelicot_CI_GITURL:=https://gitlab.inria.fr/coquelicot/coquelicot}"
: "${coquelicot_CI_ARCHIVEURL:=${coquelicot_CI_GITURL}/-/archive}"

########################################################################
# Coq-interval
########################################################################
# This is the latest release (from 3 months ago) but I don't know if
# it is compatible with Coq 8.12 since it is not in the CI.
: "${interval_CI_REF:=interval-3.4.2}"
: "${interval_CI_GITURL:=https://gitlab.inria.fr/coqinterval/interval}"
: "${interval_CI_ARCHIVEURL:=${interval_CI_GITURL}/-/archive}"

########################################################################
# Gappa stand alone tool
########################################################################
# Keeping same version from Coq 8.11 release (no new release since)
: "${gappa_tool_CI_REF:=f53e105cd73484fc76eb58ba24ead73be502c608}"
: "${gappa_tool_CI_GITURL:=https://gitlab.inria.fr/gappa/gappa}"
: "${gappa_tool_CI_ARCHIVEURL:=${gappa_tool_CI_GITURL}/-/archive}"

########################################################################
# Gappa plugin
########################################################################
# This is the latest release (from 1 month ago) but I don't know if it
# is compatible with Coq 8.12 since it is not in the CI.
: "${gappa_plugin_CI_REF:=gappalib-coq-1.4.3}"
: "${gappa_plugin_CI_GITURL:=https://gitlab.inria.fr/gappa/coq}"
: "${gappa_plugin_CI_ARCHIVEURL:=${gappa_plugin_CI_GITURL}/-/archive}"

########################################################################
# CompCert
########################################################################
# First commit compatible with Coq 8.12.  Compared to the latest
# release (3.7), it contains relatively few changes but not only bug
# fixes.  Determine what to do before releasing 8.12.0.
: "${compcert_CI_REF:=e464549037dcf94494c5aea462e6c3854b44976d}"
: "${compcert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${compcert_CI_ARCHIVEURL:=${compcert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
# This commit is very different from the latest release (which isn't
# compatible with Coq 8.12).
: "${vst_CI_REF:=815244771c92585a23363ebbff2bab7d7050e435}"
: "${vst_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${vst_CI_ARCHIVEURL:=${vst_CI_GITURL}/archive}"

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
# There's no 8.12-compatible release yet but there is an
# 8.12-compatible branch.
: "${bignums_CI_REF:=v8.12}"
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
# To Coq 8.12-specific tag or branch.  This is the latest commit on
# master and the only one compatible with Coq 8.12.  Compared to the
# latest release (1.2.1-8.11), it virtually only contains
# compatibility fixes.  Check whether there is a tag for Coq 8.12.0.
: "${equations_CI_REF:=74f048116242d7fb13cbc554522f02fe270720d2}"
: "${equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${equations_CI_ARCHIVEURL:=${equations_CI_GITURL}/archive}"

########################################################################
# Elpi + Hierarchy Builder
########################################################################
# There is no 8.12-specific branch yet.  This commit is the latest on
# coq-master and the only one compatible with Coq 8.12.  Compared to
# the latest release (1.4.0), it virtually only contains compatibility
# fixes.
: "${elpi_CI_REF:=75b82ca6826270a5d399250fd5862da7aa9c9fdd}"
: "${elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${elpi_CI_ARCHIVEURL:=${elpi_CI_GITURL}/archive}"

# This was just released and is compatible with Coq 8.12.
: "${elpi_hb_CI_REF:=v0.9.1}"
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
# This commit contains two compatibility fixes compared to the last
# released version
: "${ext_lib_CI_REF:=ad7ba4509212e032f78056a60459c2ddba8b4235}"
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
# There is no Coq 8.12-specific branch yet.  This is the latest commit
# on master and the only one that's compatible with Coq 8.12.
# Compared to the latest release (1.3.1), the new commits are only
# infrastructure changes and compatibility fixes.  Check whether a new
# tag or branch exists for Coq 8.12.0.
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
# menhir and menhirlib
########################################################################
# The latest release is from one week ago, should be compatible with
# Coq 8.12.
: "${menhir_CI_REF:=20200525}"
: "${menhir_CI_GITURL:=https://gitlab.inria.fr/fpottier/menhir}"
: "${menhir_CI_ARCHIVEURL:=${menhir_CI_GITURL}/-/archive}"

########################################################################
# aac_tactics
########################################################################
# There is not yet a Coq 8.12-specific tag but there is already a
# branch.
: "${aac_tactics_CI_REF:=v8.12}"
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
