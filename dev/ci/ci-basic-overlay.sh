#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
: "${mathcomp_CI_REF:=mathcomp-1.7.0}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"
: "${mathcomp_CI_ARCHIVEURL:=${mathcomp_CI_GITURL}/archive}"

: "${oddorder_CI_REF:=master}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order}"
: "${oddorder_CI_ARCHIVEURL:=${oddorder_CI_GITURL}/archive}"

########################################################################
# UniMath
########################################################################
: "${UniMath_CI_REF:=master}"
: "${UniMath_CI_GITURL:=https://github.com/UniMath/UniMath}"
: "${UniMath_CI_ARCHIVEURL:=${UniMath_CI_GITURL}/archive}"

########################################################################
# Unicoq + Mtac2
########################################################################
: "${unicoq_CI_REF:=master}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

: "${mtac2_CI_REF:=master-sync}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2}"
: "${mtac2_CI_ARCHIVEURL:=${mtac2_CI_GITURL}/archive}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_REF:=master}"
: "${math_classes_CI_GITURL:=https://github.com/coq-community/math-classes}"
: "${math_classes_CI_ARCHIVEURL:=${math_classes_CI_GITURL}/archive}"

: "${Corn_CI_REF:=master}"
: "${Corn_CI_GITURL:=https://github.com/coq-community/corn}"
: "${Corn_CI_ARCHIVEURL:=${Corn_CI_GITURL}/archive}"

########################################################################
# Iris
########################################################################
: "${stdpp_CI_REF:=master}"
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp}"
: "${stdpp_CI_ARCHIVEURL:=${stdpp_CI_GITURL}/-/archive}"

: "${Iris_CI_REF:=master}"
: "${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/FP/iris-coq}"
: "${Iris_CI_ARCHIVEURL:=${Iris_CI_GITURL}/-/archive}"

: "${lambdaRust_CI_REF:=master}"
: "${lambdaRust_CI_GITURL:=https://gitlab.mpi-sws.org/FP/LambdaRust-coq}"
: "${lambdaRust_CI_ARCHIVEURL:=${lambdaRust_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
: "${HoTT_CI_REF:=V8.8}"
: "${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${HoTT_CI_ARCHIVEURL:=${HoTT_CI_GITURL}/archive}"

########################################################################
# Ltac2
########################################################################
: "${ltac2_CI_REF:=0.1}"
: "${ltac2_CI_GITURL:=https://github.com/ppedrot/ltac2}"
: "${ltac2_CI_ARCHIVEURL:=${ltac2_CI_GITURL}/archive}"

########################################################################
# GeoCoq
########################################################################
: "${GeoCoq_CI_REF:=master}"
: "${GeoCoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"
: "${GeoCoq_CI_ARCHIVEURL:=${GeoCoq_CI_GITURL}/archive}"

########################################################################
# Flocq
########################################################################
: "${Flocq_CI_REF:=master}"
: "${Flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"
: "${Flocq_CI_ARCHIVEURL:=${Flocq_CI_GITURL}/-/archive}"

########################################################################
# Coquelicot
########################################################################
# ATTENTION: The archive URL might depend on the version
: "${Coquelicot_CI_REF:=coquelicot-3.0.2}"
: "${Coquelicot_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/coquelicot/coquelicot}"
: "${Coquelicot_CI_ARCHIVEURL:=https://gforge.inria.fr/frs/download.php/file/37523}"

########################################################################
# CompCert
########################################################################
# Note: The latest release version of CompCert (3.3) does not compile with Coq 8.8.1
# This is caused by a compatibility issue with OCaml 4.0.7
: "${CompCert_CI_REF:=17f9d839df12511a7e327f2840855e70af5ede47}"
: "${CompCert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${CompCert_CI_ARCHIVEURL:=${CompCert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
# Note: The latest release version of VST (2.2) does not compile with Coq 8.8.1
# Note: newer versions of VST have issues with buildability and licensing
: "${VST_CI_REF:=e49605cf1f1e5ae3bbec3d6554122427a94ae986}"
: "${VST_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${VST_CI_ARCHIVEURL:=${VST_CI_GITURL}/archive}"

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
# formal-topology
########################################################################
: "${formal_topology_CI_REF:=ci}"
: "${formal_topology_CI_GITURL:=https://github.com/bmsherman/topology}"
: "${formal_topology_CI_ARCHIVEURL:=${formal_topology_CI_GITURL}/archive}"

########################################################################
# coq-dpdgraph
########################################################################
: "${coq_dpdgraph_CI_REF:=coq-v8.8}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"
: "${coq_dpdgraph_CI_ARCHIVEURL:=${coq_dpdgraph_CI_GITURL}/archive}"

########################################################################
# CoLoR
########################################################################
: "${CoLoR_CI_REF:=master}"
: "${CoLoR_CI_GITURL:=https://github.com/fblanqui/color}"
: "${CoLoR_CI_ARCHIVEURL:=${CoLoR_CI_GITURL}/archive}"

########################################################################
# SF
########################################################################
: "${sf_lf_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/lf-current/lf.tgz}"
: "${sf_plf_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/plf-current/plf.tgz}"
: "${sf_vfa_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/vfa-current/vfa.tgz}"

########################################################################
# TLC
########################################################################
: "${tlc_CI_REF:=master}"
: "${tlc_CI_GITURL:=https://gforge.inria.fr/git/tlc/tlc}"

########################################################################
# Bignums
########################################################################
: "${bignums_CI_REF:=V8.8.0}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"
: "${bignums_CI_ARCHIVEURL:=${bignums_CI_GITURL}/archive}"

########################################################################
# bedrock2
########################################################################
: "${bedrock2_CI_REF:=master}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"
: "${bedrock2_CI_ARCHIVEURL:=${bedrock2_CI_GITURL}/archive}"

########################################################################
# Equations
########################################################################
: "${Equations_CI_REF:=v1.1-8.8}"
: "${Equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${Equations_CI_ARCHIVEURL:=${Equations_CI_GITURL}/archive}"

########################################################################
# Elpi
########################################################################
: "${Elpi_CI_REF:=coq-v8.8}"
: "${Elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${Elpi_CI_ARCHIVEURL:=${Elpi_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_REF:=master}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# ext-lib
########################################################################
# Note: This is the latest commit of the v8.8 branch as of August 31st 2018
: "${ext_lib_CI_REF:=5dd9cfa51f96fcb785c7c31d8c6bf55af5d93f27}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
: "${simple_io_CI_REF:=0.2}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################
: "${quickchick_CI_REF:=v1.0.2}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
: "${quickchick_CI_ARCHIVEURL:=${quickchick_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################
: "${menhirlib_CI_REF:=20180827}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/coq-menhirlib}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac-tactics
########################################################################
# Note: this is the latest commit of the v8.8 branch as of August 31st 2018
: "${aactactis_CI_REF:=86ac28259030649ef51460e4de2441c8a1017751}"
: "${aactactis_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aactactis_CI_ARCHIVEURL:=${aactactis_CI_GITURL}/archive}"
