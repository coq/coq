#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
: "${mathcomp_CI_REF:=master}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"
: "${mathcomp_CI_ARCHIVEURL:=${mathcomp_CI_GITURL}/archive}"

: "${fourcolor_CI_REF:=master}"
: "${fourcolor_CI_GITURL:=https://github.com/math-comp/fourcolor}"
: "${fourcolor_CI_ARCHIVEURL:=${fourcolor_CI_GITURL}/archive}"

: "${oddorder_CI_REF:=master}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order}"
: "${oddorder_CI_ARCHIVEURL:=${oddorder_CI_GITURL}/archive}"

########################################################################
# UniMath
########################################################################
: "${unimath_CI_REF:=master}"
: "${unimath_CI_GITURL:=https://github.com/UniMath/UniMath}"
: "${unimath_CI_ARCHIVEURL:=${unimath_CI_GITURL}/archive}"

########################################################################
# Unicoq + Mtac2
########################################################################
: "${unicoq_CI_REF:=master}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

: "${mtac2_CI_REF:=master}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2}"
: "${mtac2_CI_ARCHIVEURL:=${mtac2_CI_GITURL}/archive}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_REF:=master}"
: "${math_classes_CI_GITURL:=https://github.com/coq-community/math-classes}"
: "${math_classes_CI_ARCHIVEURL:=${math_classes_CI_GITURL}/archive}"

: "${corn_CI_REF:=master}"
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

: "${lambda_rust_CI_REF:=master}"
: "${lambda_rust_CI_GITURL:=https://gitlab.mpi-sws.org/iris/lambda-rust}"
: "${lambda_rust_CI_ARCHIVEURL:=${lambda_rust_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
: "${hott_CI_REF:=master}"
: "${hott_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${hott_CI_ARCHIVEURL:=${hott_CI_GITURL}/archive}"

########################################################################
# CoqHammer
########################################################################
: "${coqhammer_CI_REF:=master}"
: "${coqhammer_CI_GITURL:=https://github.com/lukaszcz/coqhammer}"
: "${coqhammer_CI_ARCHIVEURL:=${coqhammer_CI_GITURL}/archive}"

########################################################################
# GeoCoq
########################################################################
: "${geocoq_CI_REF:=master}"
: "${geocoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"
: "${geocoq_CI_ARCHIVEURL:=${geocoq_CI_GITURL}/archive}"

########################################################################
# Flocq
########################################################################
: "${flocq_CI_REF:=master}"
: "${flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"
: "${flocq_CI_ARCHIVEURL:=${flocq_CI_GITURL}/-/archive}"

########################################################################
# coq-tools
########################################################################
: "${coq_tools_CI_REF:=master}"
: "${coq_tools_CI_GITURL:=https://github.com/JasonGross/coq-tools}"
: "${coq_tools_CI_ARCHIVEURL:=${coq_tools_CI_GITURL}/archive}"

########################################################################
# Coquelicot
########################################################################
: "${coquelicot_CI_REF:=master}"
: "${coquelicot_CI_GITURL:=https://gitlab.inria.fr/coquelicot/coquelicot}"
: "${coquelicot_CI_ARCHIVEURL:=${coquelicot_CI_GITURL}/-/archive}"

########################################################################
# Coq-interval
########################################################################
: "${interval_CI_REF:=master}"
: "${interval_CI_GITURL:=https://gitlab.inria.fr/coqinterval/interval}"
: "${interval_CI_ARCHIVEURL:=${interval_CI_GITURL}/-/archive}"

########################################################################
# Gappa stand alone tool
########################################################################
: "${gappa_tool_CI_REF:=master}"
: "${gappa_tool_CI_GITURL:=https://gitlab.inria.fr/gappa/gappa}"
: "${gappa_tool_CI_ARCHIVEURL:=${gappa_tool_CI_GITURL}/-/archive}"

########################################################################
# Gappa plugin
########################################################################
: "${gappa_plugin_CI_REF:=master}"
: "${gappa_plugin_CI_GITURL:=https://gitlab.inria.fr/gappa/coq}"
: "${gappa_plugin_CI_ARCHIVEURL:=${gappa_plugin_CI_GITURL}/-/archive}"

########################################################################
# CompCert
########################################################################
: "${compcert_CI_REF:=master}"
: "${compcert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${compcert_CI_ARCHIVEURL:=${compcert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
: "${vst_CI_REF:=master}"
: "${vst_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${vst_CI_ARCHIVEURL:=${vst_CI_GITURL}/archive}"

########################################################################
# cross-crypto
########################################################################
: "${cross_crypto_CI_REF:=master}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto}"
: "${cross_crypto_CI_ARCHIVEURL:=${cross_crypto_CI_GITURL}/archive}"

########################################################################
# rewriter
########################################################################
: "${rewriter_CI_REF:=master}"
: "${rewriter_CI_GITURL:=https://github.com/mit-plv/rewriter}"
: "${rewriter_CI_ARCHIVEURL:=${rewriter_CI_GITURL}/archive}"

########################################################################
# fiat_parsers
########################################################################
: "${fiat_parsers_CI_REF:=master}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat}"
: "${fiat_parsers_CI_ARCHIVEURL:=${fiat_parsers_CI_GITURL}/archive}"

########################################################################
# fiat_crypto
########################################################################
: "${fiat_crypto_CI_REF:=master}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_CI_ARCHIVEURL:=${fiat_crypto_CI_GITURL}/archive}"

########################################################################
# coq_dpdgraph
########################################################################
: "${coq_dpdgraph_CI_REF:=coq-master}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"
: "${coq_dpdgraph_CI_ARCHIVEURL:=${coq_dpdgraph_CI_GITURL}/archive}"

########################################################################
# CoLoR
########################################################################
: "${color_CI_REF:=master}"
: "${color_CI_GITURL:=https://github.com/fblanqui/color}"
: "${color_CI_ARCHIVEURL:=${color_CI_GITURL}/archive}"

########################################################################
# TLC
########################################################################
: "${tlc_CI_REF:=master-for-coq-ci}"
: "${tlc_CI_GITURL:=https://github.com/charguer/tlc}"
: "${tlc_CI_ARCHIVEURL:=${tlc_CI_GITURL}/archive}"

########################################################################
# Bignums
########################################################################
: "${bignums_CI_REF:=master}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"
: "${bignums_CI_ARCHIVEURL:=${bignums_CI_GITURL}/archive}"

########################################################################
# coqprime
########################################################################
: "${coqprime_CI_REF:=master}"
: "${coqprime_CI_GITURL:=https://github.com/thery/coqprime}"
: "${coqprime_CI_ARCHIVEURL:=${coqprime_CI_GITURL}/archive}"

########################################################################
# bbv
########################################################################
: "${bbv_CI_REF:=master}"
: "${bbv_CI_GITURL:=https://github.com/mit-plv/bbv}"
: "${bbv_CI_ARCHIVEURL:=${bbv_CI_GITURL}/archive}"

########################################################################
# bedrock2
########################################################################
: "${bedrock2_CI_REF:=tested}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"
: "${bedrock2_CI_ARCHIVEURL:=${bedrock2_CI_GITURL}/archive}"

########################################################################
# Equations
########################################################################
: "${equations_CI_REF:=master}"
: "${equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${equations_CI_ARCHIVEURL:=${equations_CI_GITURL}/archive}"

########################################################################
# Elpi + Hierarchy Builder
########################################################################
: "${elpi_CI_REF:=coq-master}"
: "${elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${elpi_CI_ARCHIVEURL:=${elpi_CI_GITURL}/archive}"

: "${elpi_hb_CI_REF:=coq-master}"
: "${elpi_hb_CI_GITURL:=https://github.com/math-comp/hierarchy-builder}"
: "${elpi_hb_CI_ARCHIVEURL:=${elpi_hb_CI_GITURL}/archive}"

########################################################################
# Engine-Bench
########################################################################
: "${engine_bench_CI_REF:=master}"
: "${engine_bench_CI_GITURL:=https://github.com/mit-plv/engine-bench}"
: "${engine_bench_CI_ARCHIVEURL:=${engine_bench_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_REF:=master}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# ext-lib
########################################################################
: "${ext_lib_CI_REF:=master}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-community/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
: "${simple_io_CI_REF:=master}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################
: "${quickchick_CI_REF:=master}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
: "${quickchick_CI_ARCHIVEURL:=${quickchick_CI_GITURL}/archive}"

########################################################################
# reduction-effects
########################################################################
: "${reduction_effects_CI_REF:=master}"
: "${reduction_effects_CI_GITURL:=https://github.com/coq-community/reduction-effects}"
: "${reduction_effects_CI_ARCHIVEURL:=${reduction_effects_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
: "${menhirlib_CI_REF:=master}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/menhir}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac_tactics
########################################################################
: "${aac_tactics_CI_REF:=master}"
: "${aac_tactics_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aac_tactics_CI_ARCHIVEURL:=${aac_tactics_CI_GITURL}/archive}"

########################################################################
# paramcoq
########################################################################
: "${paramcoq_CI_REF:=master}"
: "${paramcoq_CI_GITURL:=https://github.com/coq-community/paramcoq}"
: "${paramcoq_CI_ARCHIVEURL:=${paramcoq_CI_GITURL}/archive}"

########################################################################
# relation_algebra
########################################################################
: "${relation_algebra_CI_REF:=master}"
: "${relation_algebra_CI_GITURL:=https://github.com/damien-pous/relation-algebra}"
: "${relation_algebra_CI_ARCHIVEURL:=${relation_algebra_CI_GITURL}/archive}"

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
: "${struct_tact_CI_REF:=master}"
: "${struct_tact_CI_GITURL:=https://github.com/uwplse/StructTact}"
: "${struct_tact_CI_ARCHIVEURL:=${struct_tact_CI_GITURL}/archive}"

: "${inf_seq_ext_CI_REF:=master}"
: "${inf_seq_ext_CI_GITURL:=https://github.com/DistributedComponents/InfSeqExt}"
: "${inf_seq_ext_CI_ARCHIVEURL:=${inf_seq_ext_CI_GITURL}/archive}"

: "${cheerios_CI_REF:=master}"
: "${cheerios_CI_GITURL:=https://github.com/uwplse/cheerios}"
: "${cheerios_CI_ARCHIVEURL:=${cheerios_CI_GITURL}/archive}"

: "${verdi_CI_REF:=master}"
: "${verdi_CI_GITURL:=https://github.com/uwplse/verdi}"
: "${verdi_CI_ARCHIVEURL:=${verdi_CI_GITURL}/archive}"

: "${verdi_raft_CI_REF:=master}"
: "${verdi_raft_CI_GITURL:=https://github.com/uwplse/verdi-raft}"
: "${verdi_raft_CI_ARCHIVEURL:=${verdi_raft_CI_GITURL}/archive}"

########################################################################
# stdlib2
########################################################################
: "${stdlib2_CI_REF:=master}"
: "${stdlib2_CI_GITURL:=https://github.com/coq/stdlib2}"
: "${stdlib2_CI_ARCHIVEURL:=${stdlib2_CI_GITURL}/archive}"

########################################################################
# argosy
########################################################################
: "${argosy_CI_REF:=master}"
: "${argosy_CI_GITURL:=https://github.com/mit-pdos/argosy}"
: "${argosy_CI_ARCHIVEURL:=${argosy_CI_GITURL}/archive}"

########################################################################
# perennial
########################################################################
: "${perennial_CI_REF:=coq/tested}"
: "${perennial_CI_GITURL:=https://github.com/mit-pdos/perennial}"
: "${perennial_CI_ARCHIVEURL:=${perennial_CI_GITURL}/archive}"

########################################################################
# metacoq
########################################################################
: "${metacoq_CI_REF:=master}"
: "${metacoq_CI_GITURL:=https://github.com/MetaCoq/metacoq}"
: "${metacoq_CI_ARCHIVEURL:=${metacoq_CI_GITURL}/archive}"

########################################################################
# SF suite
########################################################################
: "${sf_CI_REF:=master}"
: "${sf_CI_GITURL:=https://github.com/DeepSpec/sf}"
: "${sf_CI_ARCHIVEURL:=${sf_CI_GITURL}/archive}"
