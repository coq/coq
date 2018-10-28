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

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp}"
: "${stdpp_CI_ARCHIVEURL:=${stdpp_CI_GITURL}/-/archive}"

: "${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/FP/iris-coq}"
: "${Iris_CI_ARCHIVEURL:=${Iris_CI_GITURL}/-/archive}"

: "${lambdaRust_CI_REF:=master}"
: "${lambdaRust_CI_GITURL:=https://gitlab.mpi-sws.org/FP/LambdaRust-coq}"
: "${lambdaRust_CI_ARCHIVEURL:=${lambdaRust_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
: "${HoTT_CI_REF:=master}"
: "${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${HoTT_CI_ARCHIVEURL:=${HoTT_CI_GITURL}/archive}"

########################################################################
# Ltac2
########################################################################
: "${ltac2_CI_REF:=master}"
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
: "${CompCert_CI_REF:=master}"
: "${CompCert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${CompCert_CI_ARCHIVEURL:=${CompCert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################
: "${VST_CI_REF:=master}"
: "${VST_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${VST_CI_ARCHIVEURL:=${VST_CI_GITURL}/archive}"

########################################################################
# cross-crypto
########################################################################
: "${cross_crypto_CI_REF:=master}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto}"
: "${cross_crypto_CI_ARCHIVEURL:=${cross_crypto_CI_GITURL}/archive}"

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
: "${coq_dpdgraph_CI_REF:=coq-master}"
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
: "${bignums_CI_REF:=master}"
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
: "${Equations_CI_REF:=master}"
: "${Equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${Equations_CI_ARCHIVEURL:=${Equations_CI_GITURL}/archive}"

########################################################################
# Elpi
########################################################################
: "${Elpi_CI_REF:=coq-master}"
: "${Elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${Elpi_CI_ARCHIVEURL:=${Elpi_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_REF:=master}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# pidetop
########################################################################
: "${pidetop_CI_REF:=v8.9}"
: "${pidetop_CI_GITURL:=https://bitbucket.org/coqpide/pidetop}"
: "${pidetop_CI_ARCHIVEURL:=${pidetop_CI_GITURL}/get}"

########################################################################
# ext-lib
########################################################################
: "${ext_lib_CI_REF:=master}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib}"
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
# plugin_tutorial
########################################################################
: "${plugin_tutorial_CI_REF:=master}"
: "${plugin_tutorial_CI_GITURL:=https://github.com/ybertot/plugin_tutorials}"
: "${plugin_tutorial_CI_ARCHIVEURL:=${plugin_tutorial_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################
: "${menhirlib_CI_REF:=master}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/coq-menhirlib}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac-tactics
########################################################################
: "${aactactics_CI_REF:=master}"
: "${aactactics_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aactactics_CI_ARCHIVEURL:=${aactactics_CI_GITURL}/archive}"
