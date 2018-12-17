#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${mathcomp_CI_REF:=5f8d45b54aa98732ec3de43d91814459d5a2f2e4}"
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
# Latest commit on master as of Sep 27, 2018
: "${unicoq_CI_REF:=1cec038ab34e03109f5587a8aecda1f6c53495dd}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

# Latest commit on master-sync as of Sep 27, 2018
: "${mtac2_CI_REF:=e65c2560e5098df5e7333f19db97e9f39e46c3ee}"
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
# The URL for downloading a tgz snapshot of the master branch is
# https://scm.gforge.inria.fr/anonscm/gitweb?p=coquelicot/coquelicot.git;a=snapshot;h=refs/heads/master;sf=tgz
# See https://gforge.inria.fr/scm/browser.php?group_id=3599
# Since this URL doesn't fit to our standard mechanism and since Coquelicot doesn't seem to change frequently,
# we use a fixed version, which has a download path which does fit to our standard mechanism.
# ATTENTION: The archive URL might depend on the version!
: "${Coquelicot_CI_REF:=coquelicot-3.0.2}"
: "${Coquelicot_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/coquelicot/coquelicot}"
: "${Coquelicot_CI_ARCHIVEURL:=https://gforge.inria.fr/frs/download.php/file/37523}"

########################################################################
# CompCert
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${CompCert_CI_REF:=020be062488d755236f296fff760c7491e11997b}"
: "${CompCert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${CompCert_CI_ARCHIVEURL:=${CompCert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
# Latest commit on master as of Dec 10, 2018
: "${VST_CI_REF:=f6afb456db69df66c366c36b2d0218d92813f546}"
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
# Latest commit on master as of Sep 27, 2018
: "${bignums_CI_REF:=f1a63cb4cce9a79e4406275fbb0ee2269947f8d2}"
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
# Latest commit on master as of Sep 26, 2018
: "${Equations_CI_REF:=477cb9d8aac85e03dad3f992f99646e14d803a0c}"
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
: "${fcsl_pcm_CI_REF:=51ade0a882ae2ac7df071b41d468df1813504c81}"
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
# Latest commit on master as of Sep 27, 2018
: "${ext_lib_CI_REF:=a9c138921fb8c2601e64f1a1702a689120d456f3}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${simple_io_CI_REF:=e627c087ed8225d70aa7aafe882448fea31fef32}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################
# Latest commit on master as of Sep 27, 2018
: "${quickchick_CI_REF:=fae47245b75f049c462601d88e4df2e063841a3b}"
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
# Latest commit on master as of Sep 27, 2018
: "${menhirlib_CI_REF:=9e4b304bdbcc1f8d433e005a46eb10480e7ae880}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/coq-menhirlib}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac-tactics
########################################################################
# Latest commit on v8.9 as of Dec 17, 2018
: "${aactactis_CI_REF:=c469b26e409b1bde6a64546df85226079796dbe7}"
: "${aactactis_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aactactis_CI_ARCHIVEURL:=${aactactis_CI_GITURL}/archive}"
