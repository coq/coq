#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
: "${mathcomp_CI_REF:=8187ed3b12da2c164f1fc90c634b4330b796ab44}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"
: "${mathcomp_CI_ARCHIVEURL:=${mathcomp_CI_GITURL}/archive}"

: "${fourcolor_CI_REF:=4f993514270100bbc7f635bfea33e7e7138adb00}"
: "${fourcolor_CI_GITURL:=https://github.com/math-comp/fourcolor}"
: "${fourcolor_CI_ARCHIVEURL:=${fourcolor_CI_GITURL}/archive}"

: "${oddorder_CI_REF:=4ff7841213b20f1f55c1597804c7986363f57abd}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order}"
: "${oddorder_CI_ARCHIVEURL:=${oddorder_CI_GITURL}/archive}"

########################################################################
# UniMath
########################################################################
: "${unimath_CI_REF:=b2eb12b65adeffe8342ca85df135eae87558feb3}"
: "${unimath_CI_GITURL:=https://github.com/UniMath/UniMath}"
: "${unimath_CI_ARCHIVEURL:=${unimath_CI_GITURL}/archive}"

########################################################################
# Unicoq + Mtac2
########################################################################
: "${unicoq_CI_REF:=c33e66c8f2924449c7b98aab108d97b5ee105bab}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

: "${mtac2_CI_REF:=master-8.11}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2}"
: "${mtac2_CI_ARCHIVEURL:=${mtac2_CI_GITURL}/archive}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_REF:=3fceaab6b3128e2bfca5546390905c47442c4908}"
: "${math_classes_CI_GITURL:=https://github.com/coq-community/math-classes}"
: "${math_classes_CI_ARCHIVEURL:=${math_classes_CI_GITURL}/archive}"

: "${Corn_CI_REF:=3320b2d138ffe5a47892e695fedf70e09f85a0fa}"
: "${Corn_CI_GITURL:=https://github.com/coq-community/corn}"
: "${Corn_CI_ARCHIVEURL:=${Corn_CI_GITURL}/archive}"

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/iris/stdpp}"
: "${stdpp_CI_ARCHIVEURL:=${stdpp_CI_GITURL}/-/archive}"

: "${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/iris/iris}"
: "${Iris_CI_ARCHIVEURL:=${Iris_CI_GITURL}/-/archive}"

: "${lambdaRust_CI_REF:=c4a08f333e127c8d8af83c608cf8bcb6d01b7871}"
: "${lambdaRust_CI_GITURL:=https://gitlab.mpi-sws.org/iris/lambda-rust}"
: "${lambdaRust_CI_ARCHIVEURL:=${lambdaRust_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
: "${HoTT_CI_REF:=35d9de1f587117cafebf7d7b1851bb177f173783}"
: "${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${HoTT_CI_ARCHIVEURL:=${HoTT_CI_GITURL}/archive}"

########################################################################
# CoqHammer
########################################################################
: "${coqhammer_CI_REF:=00725b6ddedd44a08459d96173513a62bdae58e1}"
: "${coqhammer_CI_GITURL:=https://github.com/lukaszcz/coqhammer}"
: "${coqhammer_CI_ARCHIVEURL:=${coqhammer_CI_GITURL}/archive}"

########################################################################
# GeoCoq
########################################################################
: "${GeoCoq_CI_REF:=f5fa21da6199d871ee6d900514f6a6fc740f0a2d}"
: "${GeoCoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"
: "${GeoCoq_CI_ARCHIVEURL:=${GeoCoq_CI_GITURL}/archive}"

########################################################################
# Flocq
########################################################################
: "${Flocq_CI_REF:=7076cd30f4409b72b7bf852bf6a935eb60ca29b4}"
: "${Flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"
: "${Flocq_CI_ARCHIVEURL:=${Flocq_CI_GITURL}/-/archive}"

########################################################################
# Coquelicot
########################################################################
: "${coquelicot_CI_REF:=155e88c47e3793f1f2c4118bc1d4520abe780d74}"
: "${coquelicot_CI_GITURL:=https://gitlab.inria.fr/coquelicot/coquelicot}"
: "${coquelicot_CI_ARCHIVEURL:=${coquelicot_CI_GITURL}/-/archive}"

########################################################################
# Coq-interval
########################################################################
: "${interval_CI_REF:=839a03e1bddbafab868fbceee59abe678e32a0f3}"
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
: "${gappa_plugin_CI_REF:=07b2a6e39256b33f6b0b9f89c1e880dae51f740a}"
: "${gappa_plugin_CI_GITURL:=https://gitlab.inria.fr/gappa/coq}"
: "${gappa_plugin_CI_ARCHIVEURL:=${gappa_plugin_CI_GITURL}/-/archive}"

########################################################################
# CompCert
########################################################################
: "${compcert_CI_REF:=a99406bbd9c01dc04e79b14681a254fe22c9d424}"
: "${compcert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${compcert_CI_ARCHIVEURL:=${compcert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
: "${vst_CI_REF:=a04b451b3ef9fd99007115f7745713f6fc84d1dc}"
: "${vst_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${vst_CI_ARCHIVEURL:=${vst_CI_GITURL}/archive}"

########################################################################
# cross-crypto
########################################################################
: "${cross_crypto_CI_REF:=d9d278e941b12a49c0b58cfbe0418c85fbf743ee}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto}"
: "${cross_crypto_CI_ARCHIVEURL:=${cross_crypto_CI_GITURL}/archive}"

########################################################################
# fiat_parsers
########################################################################
: "${fiat_parsers_CI_REF:=1aa83b9a3cd68b00df4a3f69c82ea9881c602836}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat}"
: "${fiat_parsers_CI_ARCHIVEURL:=${fiat_parsers_CI_GITURL}/archive}"

########################################################################
# fiat_crypto
########################################################################
: "${fiat_crypto_CI_REF:=5674566a11eafdbee87ea2730130fe396b09add8}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_CI_ARCHIVEURL:=${fiat_crypto_CI_GITURL}/archive}"

########################################################################
# fiat_crypto_legacy
########################################################################
: "${fiat_crypto_legacy_CI_REF:=5bb5aae1b728861f7b05ab42495c7fa0f75b5151}"
: "${fiat_crypto_legacy_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_legacy_CI_ARCHIVEURL:=${fiat_crypto_legacy_CI_GITURL}/archive}"

########################################################################
# coq_dpdgraph
########################################################################
: "${coq_dpdgraph_CI_REF:=04ab42b2d991f25f73b65307b9ab5ec4cbfa30b6}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"
: "${coq_dpdgraph_CI_ARCHIVEURL:=${coq_dpdgraph_CI_GITURL}/archive}"

########################################################################
# CoLoR
########################################################################
: "${color_CI_REF:=44b6693d71f8ac72b2610f46d97b3c766ffddea5}"
: "${color_CI_GITURL:=https://github.com/fblanqui/color}"
: "${color_CI_ARCHIVEURL:=${color_CI_GITURL}/archive}"

########################################################################
# SF
########################################################################
: "${sf_lf_CI_TARURL:=https://softwarefoundations.cis.upenn.edu/lf-current/lf.tgz}"
: "${sf_plf_CI_TARURL:=https://softwarefoundations.cis.upenn.edu/plf-current/plf.tgz}"
: "${sf_vfa_CI_TARURL:=https://softwarefoundations.cis.upenn.edu/vfa-current/vfa.tgz}"

########################################################################
# TLC
########################################################################
: "${tlc_CI_REF:=3a77d66bde6fe9365c7452f082d6fb34d044c771}"
: "${tlc_CI_GITURL:=https://github.com/charguer/tlc}"
: "${tlc_CI_ARCHIVEURL:=${tlc_CI_GITURL}/archive}"

########################################################################
# Bignums
########################################################################
: "${bignums_CI_REF:=v8.11}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"
: "${bignums_CI_ARCHIVEURL:=${bignums_CI_GITURL}/archive}"

########################################################################
# bedrock2
########################################################################
: "${bedrock2_CI_REF:=2bc8f974854994c4f6330c7021cd9bb28b64bac7}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"
: "${bedrock2_CI_ARCHIVEURL:=${bedrock2_CI_GITURL}/archive}"

########################################################################
# Equations
########################################################################
: "${equations_CI_REF:=b593e3734f01c6f9c05987e4af593d2712025ae3}"
: "${equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${equations_CI_ARCHIVEURL:=${equations_CI_GITURL}/archive}"

########################################################################
# Elpi
########################################################################
: "${elpi_CI_REF:=da9ae08fccd43bff6efa44c7450a6b177bb17c0b}"
: "${elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${elpi_CI_ARCHIVEURL:=${elpi_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_REF:=5a471724b4bb72e446bc803ddcb6d2a83e0e6077}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# ext-lib
########################################################################
: "${ext_lib_CI_REF:=341323ab3ba1a4941d0944c99fc951b54294f9a7}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
: "${simple_io_CI_REF:=4cefa4b60eb5de1a9fc3be596e5da50da2e901ad}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################
: "${quickchick_CI_REF:=581d839e7ae989dae311e2669aa2527e6601253f}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
: "${quickchick_CI_ARCHIVEURL:=${quickchick_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################
: "${menhirlib_CI_REF:=ca0655b2f96057a271fb5c9a254a38d195b4a7f9}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/coq-menhirlib}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac_tactics
########################################################################
: "${aac_tactics_CI_REF:=c57960afb0c9702a8c3c12aec26534e3495bbde9}"
: "${aac_tactics_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aac_tactics_CI_ARCHIVEURL:=${aac_tactics_CI_GITURL}/archive}"

########################################################################
# paramcoq
########################################################################
: "${paramcoq_CI_REF:=v8.11}"
: "${paramcoq_CI_GITURL:=https://github.com/coq-community/paramcoq}"
: "${paramcoq_CI_ARCHIVEURL:=${paramcoq_CI_GITURL}/archive}"

########################################################################
# relation_algebra
########################################################################
: "${relation_algebra_CI_REF:=aaab2097f7da6f0909f01367e3abd77f87e0005b}"
: "${relation_algebra_CI_GITURL:=https://github.com/damien-pous/relation-algebra}"
: "${relation_algebra_CI_ARCHIVEURL:=${relation_algebra_CI_GITURL}/archive}"

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
: "${struct_tact_CI_REF:=b95f041cb83986fb0fe1f9689d7196e2f09a4839}"
: "${struct_tact_CI_GITURL:=https://github.com/uwplse/StructTact}"
: "${struct_tact_CI_ARCHIVEURL:=${struct_tact_CI_GITURL}/archive}"

: "${inf_seq_ext_CI_REF:=19f6359e65ecb872d49208f60bf8951fb76fe091}"
: "${inf_seq_ext_CI_GITURL:=https://github.com/DistributedComponents/InfSeqExt}"
: "${inf_seq_ext_CI_ARCHIVEURL:=${inf_seq_ext_CI_GITURL}/archive}"

: "${cheerios_CI_REF:=f0c7659c44999c6cfcd484dc3182affc3ff4248a}"
: "${cheerios_CI_GITURL:=https://github.com/uwplse/cheerios}"
: "${cheerios_CI_ARCHIVEURL:=${cheerios_CI_GITURL}/archive}"

: "${verdi_CI_REF:=2b94f5529eb7b8d28ef7e596383b4eec1d8343c5}"
: "${verdi_CI_GITURL:=https://github.com/uwplse/verdi}"
: "${verdi_CI_ARCHIVEURL:=${verdi_CI_GITURL}/archive}"

: "${verdi_raft_CI_REF:=51d8945e16ae976e58677ea3c423ca4b02061449}"
: "${verdi_raft_CI_GITURL:=https://github.com/uwplse/verdi-raft}"
: "${verdi_raft_CI_ARCHIVEURL:=${verdi_raft_CI_GITURL}/archive}"

########################################################################
# stdlib2
########################################################################
: "${stdlib2_CI_REF:=87767e25fbea6b38128d4b16fd62dd2edaad3503}"
: "${stdlib2_CI_GITURL:=https://github.com/coq/stdlib2}"
: "${stdlib2_CI_ARCHIVEURL:=${stdlib2_CI_GITURL}/archive}"

########################################################################
# argosy
########################################################################
: "${argosy_CI_REF:=4e98f348efb797499b06d51958d0654f07e3eb12}"
: "${argosy_CI_GITURL:=https://github.com/mit-pdos/argosy}"
: "${argosy_CI_ARCHIVEURL:=${argosy_CI_GITURL}/archive}"

########################################################################
# perennial
########################################################################
: "${perennial_CI_REF:=b420367026ec5d24b2bf38e7f986ca35af21f073}"
: "${perennial_CI_GITURL:=https://github.com/mit-pdos/perennial}"
: "${perennial_CI_ARCHIVEURL:=${perennial_CI_GITURL}/archive}"
