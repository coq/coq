#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
# Latest release tag as of April 8th 2019
: "${mathcomp_CI_REF:=mathcomp-1.8.0}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"
: "${mathcomp_CI_ARCHIVEURL:=${mathcomp_CI_GITURL}/archive}"

: "${oddorder_CI_REF:=master}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order}"
: "${oddorder_CI_ARCHIVEURL:=${oddorder_CI_GITURL}/archive}"

########################################################################
# UniMath
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${UniMath_CI_REF:=17a5f224feb42b562ded5fec79ea937dcb45764c}"
: "${UniMath_CI_GITURL:=https://github.com/UniMath/UniMath}"
: "${UniMath_CI_ARCHIVEURL:=${UniMath_CI_GITURL}/archive}"

########################################################################
# Unicoq + Mtac2
########################################################################
# This is the latest tag for 8.9 as of April 8 2019
: "${unicoq_CI_REF:=v1.3-8.9}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

# This is the latest tag for 8.9 as of April 8 2019
: "${mtac2_CI_REF:=v1.1-coq8.9}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2}"
: "${mtac2_CI_ARCHIVEURL:=${mtac2_CI_GITURL}/archive}"

########################################################################
# Mathclasses + Corn
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${math_classes_CI_REF:=0f530c713db886ab692bba49862a1cbcbebc8610}"
: "${math_classes_CI_GITURL:=https://github.com/coq-community/math-classes}"
: "${math_classes_CI_ARCHIVEURL:=${math_classes_CI_GITURL}/archive}"

# Latest commit on master as of Sep 27, 2018
: "${Corn_CI_REF:=f505e489829a968074f53fe18b70a292ad94a9d0}"
: "${Corn_CI_GITURL:=https://github.com/coq-community/corn}"
: "${Corn_CI_ARCHIVEURL:=${Corn_CI_GITURL}/archive}"

########################################################################
# Iris
########################################################################
# std++ commit pinned in Iris
: "${stdpp_CI_REF:=4fb641edc8d74fbba01fed33d9acbc8a423ea601}"
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp}"
: "${stdpp_CI_ARCHIVEURL:=${stdpp_CI_GITURL}/-/archive}"

# Iris commit pinned in LambdaRust
: "${Iris_CI_REF:=85425d47be677d05d74caff5e1a8a85289d96ae1}"
: "${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/FP/iris-coq}"
: "${Iris_CI_ARCHIVEURL:=${Iris_CI_GITURL}/-/archive}"

# Latest commit on master as of Sep 27, 2018
: "${lambdaRust_CI_REF:=fd46e6625eef509a80896dccf6c976545b17ab90}"
: "${lambdaRust_CI_GITURL:=https://gitlab.mpi-sws.org/FP/LambdaRust-coq}"
: "${lambdaRust_CI_ARCHIVEURL:=${lambdaRust_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
# Latest commit on master as of Sep 3, 2018
: "${HoTT_CI_REF:=333face272e39175a1b342e14c86c316f572f51f}"
: "${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${HoTT_CI_ARCHIVEURL:=${HoTT_CI_GITURL}/archive}"

########################################################################
# Ltac2
########################################################################
# The v8.9 branch looks unmaintained-
# the last two commits (as of April 4 2019) are:
# Commits on Oct 23, 2018
# Commits on Jul 2, 2018
# master does not build
: "${ltac2_CI_REF:=v8.9}"
: "${ltac2_CI_GITURL:=https://github.com/ppedrot/ltac2}"
: "${ltac2_CI_ARCHIVEURL:=${ltac2_CI_GITURL}/archive}"

########################################################################
# GeoCoq
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${GeoCoq_CI_REF:=a13b48840898fec207b382ab42c0bf0b2f62024b}"
: "${GeoCoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"
: "${GeoCoq_CI_ARCHIVEURL:=${GeoCoq_CI_GITURL}/archive}"

########################################################################
# Flocq
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${Flocq_CI_REF:=ff6fc12f269ca055b7b6fd88247ac2697ff6e687}"
: "${Flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"
: "${Flocq_CI_ARCHIVEURL:=${Flocq_CI_GITURL}/-/archive}"

########################################################################
# Coquelicot
########################################################################
# Latest release version as of April 8th, 2019
# ATTENTION: The archive URL does depend on the version - see notes on Gappa_Tool!
: "${Coquelicot_CI_REF:=coquelicot-3.0.2}"
: "${Coquelicot_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/coquelicot/coquelicot}"
: "${Coquelicot_CI_ARCHIVEURL:=https://gforge.inria.fr/frs/download.php/file/37523}"

########################################################################
# Coq-interval
########################################################################
# Here the same applies as for Coquelicot => we are using a fixed version URL
: "${Interval_CI_REF:=interval-3.4.0}"
: "${Interval_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/coq-interval/coq-interval}"
: "${Interval_CI_ARCHIVEURL:=https://gforge.inria.fr/frs/download.php/file/37524}"

########################################################################
# Gappa stand alone tool
########################################################################
# Here the same applies as for Coquelicot => we are using a fixed version URL
# ATTENTION: The archive URL does depend on the version e.g.
# https://gforge.inria.fr/frs/download.php/file/37624/gappa-1.3.3.tar.gz
# https://gforge.inria.fr/frs/download.php/file/37918/gappa-1.3.4.tar.gz
# ATTENTION: Mixing paths, e.g.
# https://gforge.inria.fr/frs/download.php/file/37624/gappa-1.3.4.tar.gz
# Doesn't give an error, but one gets a wrong file (1.3.3 in the example above)
: "${Gappa_Tool_CI_REF:=gappa-1.3.4}"
: "${Gappa_Tool_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/gappa/gappa}"
: "${Gappa_Tool_CI_ARCHIVEURL:=https://gforge.inria.fr/frs/download.php/file/37918}"

########################################################################
# Gappa plugin
########################################################################
# Here the same applies as for Coquelicot => we are using a fixed version URL
# ATTENTION: The archive URL does depend on the version - see notes om Gappa_Tool!
: "${Gappa_Plugin_CI_REF:=gappalib-coq-1.4.1}"
: "${Gappa_Plugin_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/gappa/coq}"
: "${Gappa_Plugin_CI_ARCHIVEURL:=https://gforge.inria.fr/frs/download.php/file/37917}"

########################################################################
# CompCert
########################################################################
# Latest release tag as of April 8th, 2019
: "${CompCert_CI_REF:=v3.5}"
: "${CompCert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${CompCert_CI_ARCHIVEURL:=${CompCert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
# Latest release tag as of April 8th 2019
: "${VST_CI_REF:=v2.3}"
: "${VST_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${VST_CI_ARCHIVEURL:=${VST_CI_GITURL}/archive}"

########################################################################
# cross-crypto
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${cross_crypto_CI_REF:=453da7e0541798f36d82b6c67a3f4461cd5dc773}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto}"
: "${cross_crypto_CI_ARCHIVEURL:=${cross_crypto_CI_GITURL}/archive}"

########################################################################
# fiat_parsers
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${fiat_parsers_CI_REF:=a41e7ee1c5152aecedb354a112d5c8121a499d30}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat}"
: "${fiat_parsers_CI_ARCHIVEURL:=${fiat_parsers_CI_GITURL}/archive}"

########################################################################
# fiat_crypto
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${fiat_crypto_CI_REF:=059f186db67852ac17de78dab1987aab77dd4bdb}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_CI_ARCHIVEURL:=${fiat_crypto_CI_GITURL}/archive}"

########################################################################
# formal-topology
########################################################################
# Latest commit on ci as of Sep 27, 2018
: "${formal_topology_CI_REF:=a2f1aa04db253e4f90fb2aae724cfca42ccd53ab}"
: "${formal_topology_CI_GITURL:=https://github.com/bmsherman/topology}"
: "${formal_topology_CI_ARCHIVEURL:=${formal_topology_CI_GITURL}/archive}"

########################################################################
# coq-dpdgraph
########################################################################
# Latest commit on coq-master as of Sep 27, 2018
: "${coq_dpdgraph_CI_REF:=e14e2bc0108a593f7c64d9af3fc4aec9e8fb1397}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"
: "${coq_dpdgraph_CI_ARCHIVEURL:=${coq_dpdgraph_CI_GITURL}/archive}"

########################################################################
# CoLoR
########################################################################
# Latest commit on master as of Nov 5, 2018
: "${CoLoR_CI_REF:=4ce3a9fb5f58501aef3c0727c8ba8cc38917399d}"
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
# Latest commit on master as of Sep 27, 2018
: "${tlc_CI_REF:=6bce3c31e5c74d9f953de3620deadd9f4cc04023}"
: "${tlc_CI_GITURL:=https://gforge.inria.fr/git/tlc/tlc}"

########################################################################
# Bignums
########################################################################
# There is no 8.9 branch
# Below is the latest commit (Feb 4, 2019) on master as of April 4, 2019
# 0cd435d0a3c731605536c83d0a731c3fc336cce7 => fails (requires Cyclic63)
# This is the latest working commit (Feb 1, 2019) on master as of April 4, 2019
: "${bignums_CI_REF:=5a7ba3d02d8c095ce31fc5f0a0dbc118c58dd433}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"
: "${bignums_CI_ARCHIVEURL:=${bignums_CI_GITURL}/archive}"

########################################################################
# bedrock2
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${bedrock2_CI_REF:=cbf50671ba2d9235060d4e4747d0860f127f3995}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"
: "${bedrock2_CI_ARCHIVEURL:=${bedrock2_CI_GITURL}/archive}"

########################################################################
# Equations
########################################################################
# Latest 8.9 release tag  as of April 8th, 2019
: "${Equations_CI_REF:=v1.2-beta2-8.9}"
: "${Equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${Equations_CI_ARCHIVEURL:=${Equations_CI_GITURL}/archive}"

########################################################################
# Elpi
########################################################################
: "${Elpi_CI_REF:=coq-v8.9}"
: "${Elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${Elpi_CI_ARCHIVEURL:=${Elpi_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${fcsl_pcm_CI_REF:=v1.1.0}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# pidetop
########################################################################
# Latest commit on v8.9 as of Sep 27, 2018
: "${pidetop_CI_REF:=ef42320bc0ab75f313e9476e8c8c945ae2116cb5}"
: "${pidetop_CI_GITURL:=https://bitbucket.org/coqpide/pidetop}"
: "${pidetop_CI_ARCHIVEURL:=${pidetop_CI_GITURL}/get}"

########################################################################
# ext-lib
########################################################################
# Latest non beta tag as of April 8th 2019
: "${ext_lib_CI_REF:=v0.10.1}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
# Latest release tag as of April 8th 2019
: "${simple_io_CI_REF:=1.0.0}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################
# Latest version (March 2019) on 8.9 branch as of April 8th, 2019
: "${quickchick_CI_REF:=34a63b6a61564b99892917441fd35143dc0d10e2}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
: "${quickchick_CI_ARCHIVEURL:=${quickchick_CI_GITURL}/archive}"

########################################################################
# plugin_tutorial
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${plugin_tutorial_CI_REF:=b303b75c18734accc9cd7efe82307b0424426e3f}"
: "${plugin_tutorial_CI_GITURL:=https://github.com/ybertot/plugin_tutorials}"
: "${plugin_tutorial_CI_ARCHIVEURL:=${plugin_tutorial_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################
# Latest commit on master as of April 8th, 2019
# Note: the latest release tag is quite old (August 2018)
#       and there seem to be significant changes since then
: "${menhirlib_CI_REF:=f0842e17a90366c8e328e9a2c2f089013887edc5}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/coq-menhirlib}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac-tactics
########################################################################
# Latest commit on v8.9 as of April 8th, 2019
: "${aactactis_CI_REF:=069dc3bd125ca18f5712759d54edcf9addb4cdd4}"
: "${aactactis_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aactactis_CI_ARCHIVEURL:=${aactactis_CI_GITURL}/archive}"
