#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
: "${mathcomp_CI_BRANCH:=master}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"

########################################################################
# UniMath
########################################################################
: "${UniMath_CI_BRANCH:=master}"
: "${UniMath_CI_GITURL:=https://github.com/UniMath/UniMath}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_BRANCH:=master}"
: "${math_classes_CI_GITURL:=https://github.com/math-classes/math-classes}"

: "${Corn_CI_BRANCH:=master}"
: "${Corn_CI_GITURL:=https://github.com/c-corn/corn}"

########################################################################
# Iris
########################################################################
: "${stdpp_CI_BRANCH:=master}"
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp}"

: "${Iris_CI_BRANCH:=master}"
: "${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/FP/iris-coq}"

: "${lambdaRust_CI_BRANCH:=master}"
: "${lambdaRust_CI_GITURL:=https://gitlab.mpi-sws.org/FP/LambdaRust-coq}"

########################################################################
# HoTT
########################################################################
: "${HoTT_CI_BRANCH:=V8.8}"
: "${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT}"

########################################################################
# Ltac2
########################################################################
: "${ltac2_CI_BRANCH:=v8.8}"
: "${ltac2_CI_GITURL:=https://github.com/ppedrot/ltac2}"

########################################################################
# GeoCoq
########################################################################
: "${GeoCoq_CI_BRANCH:=master}"
: "${GeoCoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"

########################################################################
# Flocq
########################################################################
: "${Flocq_CI_BRANCH:=master}"
: "${Flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"

########################################################################
# Coquelicot
########################################################################
: "${Coquelicot_CI_BRANCH:=master}"
: "${Coquelicot_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/coquelicot/coquelicot}"

########################################################################
# CompCert
########################################################################
: "${CompCert_CI_BRANCH:=master}"
: "${CompCert_CI_GITURL:=https://github.com/AbsInt/CompCert}"

########################################################################
# VST
########################################################################
: "${VST_CI_BRANCH:=master}"
: "${VST_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"

########################################################################
# fiat_parsers
########################################################################
: "${fiat_parsers_CI_BRANCH:=master}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat}"

########################################################################
# fiat_crypto
########################################################################
: "${fiat_crypto_CI_BRANCH:=master}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"

########################################################################
# formal-topology
########################################################################
: "${formal_topology_CI_BRANCH:=ci}"
: "${formal_topology_CI_GITURL:=https://github.com/bmsherman/topology}"

########################################################################
# coq-dpdgraph
########################################################################
: "${coq_dpdgraph_CI_BRANCH:=coq-v8.8}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"

########################################################################
# CoLoR
########################################################################
: "${CoLoR_CI_BRANCH:=master}"
: "${CoLoR_CI_GITURL:=https://github.com/fblanqui/color}"

########################################################################
# SF
########################################################################
: "${sf_lf_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/lf-current/lf.tgz}"
: "${sf_plf_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/plf-current/plf.tgz}"
: "${sf_vfa_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/vfa-current/vfa.tgz}"

########################################################################
# TLC
########################################################################
: "${tlc_CI_BRANCH:=master}"
: "${tlc_CI_GITURL:=https://gforge.inria.fr/git/tlc/tlc}"

########################################################################
# Bignums
########################################################################
: "${bignums_CI_BRANCH:=v8.8}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"

########################################################################
# bedrock2
########################################################################
: "${bedrock2_CI_BRANCH:=master}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"

########################################################################
# Equations
########################################################################
: "${Equations_CI_BRANCH:=8.8}"
: "${Equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"

########################################################################
# Elpi
########################################################################
: "${Elpi_CI_BRANCH:=coq-v8.8}"
: "${Elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_BRANCH:=master}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"

########################################################################
# ext-lib
########################################################################
: "${ext_lib_CI_BRANCH:=master}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib}"

########################################################################
# simple-io
########################################################################
: "${simple_io_CI_BRANCH:=0.2}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"

########################################################################
# quickchick
########################################################################
: "${quickchick_CI_BRANCH:=8.8}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
