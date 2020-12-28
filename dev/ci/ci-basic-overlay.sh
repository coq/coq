#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
: "${mathcomp_CI_REF:=mathcomp-1.12.0}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"
: "${mathcomp_CI_ARCHIVEURL:=${mathcomp_CI_GITURL}/archive}"

: "${fourcolor_CI_REF:=v1.2.3}"
: "${fourcolor_CI_GITURL:=https://github.com/math-comp/fourcolor}"
: "${fourcolor_CI_ARCHIVEURL:=${fourcolor_CI_GITURL}/archive}"

: "${oddorder_CI_REF:=mathcomp-odd-order.1.12.0}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order}"
: "${oddorder_CI_ARCHIVEURL:=${oddorder_CI_GITURL}/archive}"

########################################################################
# UniMath
########################################################################
: "${unimath_CI_REF:=7197152b65e8d5daaf77df679652eec980d67f09}"
: "${unimath_CI_GITURL:=https://github.com/UniMath/UniMath}"
: "${unimath_CI_ARCHIVEURL:=${unimath_CI_GITURL}/archive}"

########################################################################
# Unicoq + Mtac2
########################################################################
: "${unicoq_CI_REF:=v1.5-8.13}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

: "${mtac2_CI_REF:=v1.4-coq8.13}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2}"
: "${mtac2_CI_ARCHIVEURL:=${mtac2_CI_GITURL}/archive}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_REF:=ed61829877a6fc8132e01182ac5615908078b8e7}"
: "${math_classes_CI_GITURL:=https://github.com/coq-community/math-classes}"
: "${math_classes_CI_ARCHIVEURL:=${math_classes_CI_GITURL}/archive}"

: "${corn_CI_REF:=643fc124e472c9bc4a8324190892cab1555f4577}"
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

: "${autosubst_CI_REF:=e5bf249d7912a185c7f9f69af1a065daa4284f34}"
: "${autosubst_CI_GITURL:=https://github.com/coq-community/autosubst}"
: "${autosubst_CI_ARCHIVEURL:=${autosubst_CI_GITURL}/archive}"

: "${iris_string_ident_CI_REF:=b077370ac854e8af45f8ca5a610ee2fe30e84406}"
: "${iris_string_ident_CI_GITURL:=https://gitlab.mpi-sws.org/iris/string-ident}"
: "${iris_string_ident_CI_ARCHIVEURL:=${iris_string_ident_CI_GITURL}/-/archive}"

: "${iris_examples_CI_REF:=72db5f43286f199c380f606b04da1b6f22317869}"
: "${iris_examples_CI_GITURL:=https://gitlab.mpi-sws.org/iris/examples}"
: "${iris_examples_CI_ARCHIVEURL:=${iris_examples_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
: "${hott_CI_REF:=756ff79da22d0804194145db775865c11c14aa48}"
: "${hott_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${hott_CI_ARCHIVEURL:=${hott_CI_GITURL}/archive}"

########################################################################
# CoqHammer
########################################################################
: "${coqhammer_CI_REF:=889f3520365e0c54dc2e8fe972afdf030d8b9d14}"
: "${coqhammer_CI_GITURL:=https://github.com/lukaszcz/coqhammer}"
: "${coqhammer_CI_ARCHIVEURL:=${coqhammer_CI_GITURL}/archive}"

########################################################################
# GeoCoq
########################################################################
: "${geocoq_CI_REF:=290642eff83097858f99084da9a149b021887473}"
: "${geocoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"
: "${geocoq_CI_ARCHIVEURL:=${geocoq_CI_GITURL}/archive}"

########################################################################
# Flocq
########################################################################
: "${flocq_CI_REF:=flocq-3.3.1}"
: "${flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"
: "${flocq_CI_ARCHIVEURL:=${flocq_CI_GITURL}/-/archive}"

########################################################################
# coq-performance-tests
########################################################################
: "${coq_performance_tests_CI_REF:=96b6414de9b08d2dd7e3e5ad1f591a94b303b06c}"
: "${coq_performance_tests_CI_GITURL:=https://github.com/coq-community/coq-performance-tests}"
: "${coq_performance_tests_CI_ARCHIVEURL:=${coq_performance_tests_CI_GITURL}/archive}"

########################################################################
# coq-tools
########################################################################
: "${coq_tools_CI_REF:=762df647adc1696a5fc255ab9e12ddf474245bca}"
: "${coq_tools_CI_GITURL:=https://github.com/JasonGross/coq-tools}"
: "${coq_tools_CI_ARCHIVEURL:=${coq_tools_CI_GITURL}/archive}"

########################################################################
# Coquelicot
########################################################################
: "${coquelicot_CI_REF:=coquelicot-3.1.0}"
: "${coquelicot_CI_GITURL:=https://gitlab.inria.fr/coquelicot/coquelicot}"
: "${coquelicot_CI_ARCHIVEURL:=${coquelicot_CI_GITURL}/-/archive}"

########################################################################
# Coq-interval
########################################################################
: "${interval_CI_REF:=interval-4.1.0}"
: "${interval_CI_GITURL:=https://gitlab.inria.fr/coqinterval/interval}"
: "${interval_CI_ARCHIVEURL:=${interval_CI_GITURL}/-/archive}"

########################################################################
# Gappa stand alone tool
########################################################################
: "${gappa_tool_CI_REF:=ba4dbb3ef66bbdd9d1f3d660a293515df0b57b43}"
: "${gappa_tool_CI_GITURL:=https://gitlab.inria.fr/gappa/gappa}"
: "${gappa_tool_CI_ARCHIVEURL:=${gappa_tool_CI_GITURL}/-/archive}"

########################################################################
# Gappa plugin
########################################################################
: "${gappa_plugin_CI_REF:=gappalib-coq-1.4.5}"
: "${gappa_plugin_CI_GITURL:=https://gitlab.inria.fr/gappa/coq}"
: "${gappa_plugin_CI_ARCHIVEURL:=${gappa_plugin_CI_GITURL}/-/archive}"

########################################################################
# CompCert
########################################################################
: "${compcert_CI_REF:=v3.8}"
: "${compcert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${compcert_CI_ARCHIVEURL:=${compcert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
: "${vst_CI_REF:=ebcd978765a8211d545c8efd2114dec75a991720}"
: "${vst_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${vst_CI_ARCHIVEURL:=${vst_CI_GITURL}/archive}"

########################################################################
# cross-crypto
########################################################################
: "${cross_crypto_CI_REF:=330aff9e4316b6c20147ad9743af08ae4e7e10f5}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto}"
: "${cross_crypto_CI_ARCHIVEURL:=${cross_crypto_CI_GITURL}/archive}"

########################################################################
# rewriter
########################################################################
: "${rewriter_CI_REF:=fe324e8d1f77a9d991dfcdba39456c6923153c52}"
: "${rewriter_CI_GITURL:=https://github.com/mit-plv/rewriter}"
: "${rewriter_CI_ARCHIVEURL:=${rewriter_CI_GITURL}/archive}"

########################################################################
# fiat_parsers
########################################################################
: "${fiat_parsers_CI_REF:=ef8381e3f78242b2bd80553b9734f5337ad279da}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat}"
: "${fiat_parsers_CI_ARCHIVEURL:=${fiat_parsers_CI_GITURL}/archive}"

########################################################################
# fiat_crypto
########################################################################
: "${fiat_crypto_CI_REF:=5a18e113ddede752163ac6c402e7bbfdee28a8c0}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_CI_ARCHIVEURL:=${fiat_crypto_CI_GITURL}/archive}"

########################################################################
# fiat_crypto_legacy
########################################################################
: "${fiat_crypto_legacy_CI_REF:=c5d9f3aaddf05c6ae15385485de594ba18b8cd12}"
: "${fiat_crypto_legacy_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_legacy_CI_ARCHIVEURL:=${fiat_crypto_legacy_CI_GITURL}/archive}"

########################################################################
# coq_dpdgraph
########################################################################
: "${coq_dpdgraph_CI_REF:=f12bf892561ccffe5382d97ae2684a7dae326e64}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"
: "${coq_dpdgraph_CI_ARCHIVEURL:=${coq_dpdgraph_CI_GITURL}/archive}"

########################################################################
# CoLoR
########################################################################
: "${color_CI_REF:=0207202ed802f20a08ef07dea0e0d2b5715cabd1}"
: "${color_CI_GITURL:=https://github.com/fblanqui/color}"
: "${color_CI_ARCHIVEURL:=${color_CI_GITURL}/archive}"

########################################################################
# TLC
########################################################################
: "${tlc_CI_REF:=f74b0511868483a3b896cfb0fd4eb7a1fb2239c6}"
: "${tlc_CI_GITURL:=https://github.com/charguer/tlc}"
: "${tlc_CI_ARCHIVEURL:=${tlc_CI_GITURL}/archive}"

########################################################################
# Bignums
########################################################################
: "${bignums_CI_REF:=V8.13.0}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"
: "${bignums_CI_ARCHIVEURL:=${bignums_CI_GITURL}/archive}"

########################################################################
# coqprime
########################################################################
: "${coqprime_CI_REF:=84e42b453e4e47f0d008d80890d06e234d226993}"
: "${coqprime_CI_GITURL:=https://github.com/thery/coqprime}"
: "${coqprime_CI_ARCHIVEURL:=${coqprime_CI_GITURL}/archive}"

########################################################################
# bbv
########################################################################
: "${bbv_CI_REF:=4227af1aec62afd032149f5c063cfa93b0242ca0}"
: "${bbv_CI_GITURL:=https://github.com/mit-plv/bbv}"
: "${bbv_CI_ARCHIVEURL:=${bbv_CI_GITURL}/archive}"

########################################################################
# bedrock2
########################################################################
: "${bedrock2_CI_REF:=9ca3d0cfe65a99c706173520de380e4fe5b0566b}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"
: "${bedrock2_CI_ARCHIVEURL:=${bedrock2_CI_GITURL}/archive}"

########################################################################
# Equations
########################################################################
: "${equations_CI_REF:=v1.2.3-8.13}"
: "${equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${equations_CI_ARCHIVEURL:=${equations_CI_GITURL}/archive}"

########################################################################
# Elpi + Hierarchy Builder
########################################################################
: "${elpi_CI_REF:=v1.8.1}"
: "${elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${elpi_CI_ARCHIVEURL:=${elpi_CI_GITURL}/archive}"

: "${elpi_hb_CI_REF:=v1.0.0}"
: "${elpi_hb_CI_GITURL:=https://github.com/math-comp/hierarchy-builder}"
: "${elpi_hb_CI_ARCHIVEURL:=${elpi_hb_CI_GITURL}/archive}"

########################################################################
# Engine-Bench
########################################################################
: "${engine_bench_CI_REF:=45f456e4c3b37704c6ff83ef072dc1260fef8f43}"
: "${engine_bench_CI_GITURL:=https://github.com/mit-plv/engine-bench}"
: "${engine_bench_CI_ARCHIVEURL:=${engine_bench_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_REF:=041d120f1fcc5797f06928911836c892f99b4a85}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# ext-lib
########################################################################
: "${ext_lib_CI_REF:=v0.11.3}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-community/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
: "${simple_io_CI_REF:=770d156e05be73419cdd83d0e29de8d6e1d11f5c}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################
: "${quickchick_CI_REF:=v1.5.0}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
: "${quickchick_CI_ARCHIVEURL:=${quickchick_CI_GITURL}/archive}"

########################################################################
# reduction-effects
########################################################################
: "${reduction_effects_CI_REF:=7cf41546f2d15ea3a4eeeb68695b288db2d9e09a}"
: "${reduction_effects_CI_GITURL:=https://github.com/coq-community/reduction-effects}"
: "${reduction_effects_CI_ARCHIVEURL:=${reduction_effects_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
: "${menhirlib_CI_REF:=20201122}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/menhir}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac_tactics
########################################################################
: "${aac_tactics_CI_REF:=v8.13.0}"
: "${aac_tactics_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aac_tactics_CI_ARCHIVEURL:=${aac_tactics_CI_GITURL}/archive}"

########################################################################
# paramcoq
########################################################################
: "${paramcoq_CI_REF:=v1.1.2+coq8.13}"
: "${paramcoq_CI_GITURL:=https://github.com/coq-community/paramcoq}"
: "${paramcoq_CI_ARCHIVEURL:=${paramcoq_CI_GITURL}/archive}"

########################################################################
# relation_algebra
########################################################################
: "${relation_algebra_CI_REF:=afd9f5d5265e9e23a613d325dfd053f19cf07e91}"
: "${relation_algebra_CI_GITURL:=https://github.com/damien-pous/relation-algebra}"
: "${relation_algebra_CI_ARCHIVEURL:=${relation_algebra_CI_GITURL}/archive}"

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
: "${struct_tact_CI_REF:=f8d4f8a0e04df0522a839462e725a48d54145b48}"
: "${struct_tact_CI_GITURL:=https://github.com/uwplse/StructTact}"
: "${struct_tact_CI_ARCHIVEURL:=${struct_tact_CI_GITURL}/archive}"

: "${inf_seq_ext_CI_REF:=91b2d9bdc580c7ccb5bf2f50fffb6ebabab2715c}"
: "${inf_seq_ext_CI_GITURL:=https://github.com/DistributedComponents/InfSeqExt}"
: "${inf_seq_ext_CI_ARCHIVEURL:=${inf_seq_ext_CI_GITURL}/archive}"

: "${cheerios_CI_REF:=9c7f66e57b91f706d70afa8ed99d64ed98ab367d}"
: "${cheerios_CI_GITURL:=https://github.com/uwplse/cheerios}"
: "${cheerios_CI_ARCHIVEURL:=${cheerios_CI_GITURL}/archive}"

: "${verdi_CI_REF:=35508f2af94f9da979ece0cbdfa191019f2c5478}"
: "${verdi_CI_GITURL:=https://github.com/uwplse/verdi}"
: "${verdi_CI_ARCHIVEURL:=${verdi_CI_GITURL}/archive}"

: "${verdi_raft_CI_REF:=f3cedc031580dfd5564408b898f6c21000e82a86}"
: "${verdi_raft_CI_GITURL:=https://github.com/uwplse/verdi-raft}"
: "${verdi_raft_CI_ARCHIVEURL:=${verdi_raft_CI_GITURL}/archive}"

########################################################################
# stdlib2
########################################################################
: "${stdlib2_CI_REF:=54e057ea7023d058e57169a3bceaab708a5f7d26}"
: "${stdlib2_CI_GITURL:=https://github.com/coq/stdlib2}"
: "${stdlib2_CI_ARCHIVEURL:=${stdlib2_CI_GITURL}/archive}"

########################################################################
# argosy
########################################################################
: "${argosy_CI_REF:=63dd6e6d046e3dde072ae1b6862639a8f62b1213}"
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
: "${metacoq_CI_REF:=1591d9c5d8f62ae4ccc3b030d9c5c1817c76ef91}"
: "${metacoq_CI_GITURL:=https://github.com/MetaCoq/metacoq}"
: "${metacoq_CI_ARCHIVEURL:=${metacoq_CI_GITURL}/archive}"

########################################################################
# SF suite
########################################################################
: "${sf_CI_REF:=cced6f0df38b97fdd45111681410877fee429c4a}"
: "${sf_CI_GITURL:=https://github.com/DeepSpec/sf}"
: "${sf_CI_ARCHIVEURL:=${sf_CI_GITURL}/archive}"

########################################################################
# Coqtail
########################################################################
: "${coqtail_CI_REF:=5e40da6c7119bfc31b3737d7ced2b8098f56a99f}"
: "${coqtail_CI_GITURL:=https://github.com/whonore/Coqtail}"
: "${coqtail_CI_ARCHIVEURL:=${coqtail_CI_GITURL}/archive}"
