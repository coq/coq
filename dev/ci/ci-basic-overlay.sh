#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################
: "${mathcomp_CI_BRANCH:=master}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp.git}"
: "${oddorder_CI_BRANCH:=master}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order.git}"

########################################################################
# UniMath
########################################################################
: "${UniMath_CI_BRANCH:=master}"
: "${UniMath_CI_GITURL:=https://github.com/UniMath/UniMath.git}"

########################################################################
# Unicoq + Mtac2
########################################################################
: "${unicoq_CI_BRANCH:=master}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq.git}"

: "${mtac2_CI_BRANCH:=master-sync}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2.git}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_BRANCH:=master}"
: "${math_classes_CI_GITURL:=https://github.com/math-classes/math-classes.git}"

: "${Corn_CI_BRANCH:=master}"
: "${Corn_CI_GITURL:=https://github.com/c-corn/corn.git}"

########################################################################
# Iris
########################################################################
: "${stdpp_CI_BRANCH:=master}"
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp.git}"

: "${Iris_CI_BRANCH:=master}"
: "${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/FP/iris-coq.git}"

: "${lambdaRust_CI_BRANCH:=master}"
: "${lambdaRust_CI_GITURL:=https://gitlab.mpi-sws.org/FP/LambdaRust-coq.git}"

########################################################################
# HoTT
########################################################################
: "${HoTT_CI_BRANCH:=master}"
: "${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT.git}"

########################################################################
# Ltac2
########################################################################
: "${ltac2_CI_BRANCH:=master}"
: "${ltac2_CI_GITURL:=https://github.com/ppedrot/ltac2.git}"

########################################################################
# GeoCoq
########################################################################
: "${GeoCoq_CI_BRANCH:=master}"
: "${GeoCoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq.git}"

########################################################################
# Flocq
########################################################################
: "${Flocq_CI_BRANCH:=master}"
: "${Flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq.git}"

########################################################################
# Coquelicot
########################################################################
: "${Coquelicot_CI_BRANCH:=master}"
: "${Coquelicot_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/coquelicot/coquelicot.git}"

########################################################################
# CompCert
########################################################################
: "${CompCert_CI_BRANCH:=master}"
: "${CompCert_CI_GITURL:=https://github.com/AbsInt/CompCert.git}"

########################################################################
# VST
########################################################################
: "${VST_CI_BRANCH:=master}"
: "${VST_CI_GITURL:=https://github.com/PrincetonUniversity/VST.git}"

########################################################################
# cross-crypto
########################################################################
: "${cross_crypto_CI_BRANCH:=master}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto.git}"

########################################################################
# fiat_parsers
########################################################################
: "${fiat_parsers_CI_BRANCH:=master}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat.git}"

########################################################################
# fiat_crypto
########################################################################
: "${fiat_crypto_CI_BRANCH:=master}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto.git}"

########################################################################
# formal-topology
########################################################################
: "${formal_topology_CI_BRANCH:=ci}"
: "${formal_topology_CI_GITURL:=https://github.com/bmsherman/topology.git}"

########################################################################
# coq-dpdgraph
########################################################################
: "${coq_dpdgraph_CI_BRANCH:=coq-trunk}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph.git}"

########################################################################
# CoLoR
########################################################################
: "${CoLoR_CI_BRANCH:=master}"
: "${CoLoR_CI_GITURL:=https://github.com/fblanqui/color.git}"

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
: "${tlc_CI_GITURL:=https://gforge.inria.fr/git/tlc/tlc.git}"

########################################################################
# Bignums
########################################################################
: "${bignums_CI_BRANCH:=master}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums.git}"

########################################################################
# Equations
########################################################################
: "${Equations_CI_BRANCH:=master}"
: "${Equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations.git}"

########################################################################
# Elpi
########################################################################
: "${Elpi_CI_BRANCH:=coq-master}"
: "${Elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi.git}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_BRANCH:=master}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm.git}"

########################################################################
# pidetop
########################################################################
: "${pidetop_CI_BRANCH:=v8.9}"
: "${pidetop_CI_GITURL:=https://bitbucket.org/coqpide/pidetop.git}"

########################################################################
# ext-lib
########################################################################
: "${ext_lib_CI_BRANCH:=master}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib.git}"

########################################################################
# quickchick
########################################################################
: "${quickchick_CI_BRANCH:=master}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick.git}"
