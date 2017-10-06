#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

########################################################################
# MathComp
########################################################################
: ${mathcomp_CI_BRANCH:=master}
: ${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp.git}

########################################################################
# UniMath
########################################################################
: ${UniMath_CI_BRANCH:=master}
: ${UniMath_CI_GITURL:=https://github.com/UniMath/UniMath.git}

########################################################################
# Unicoq + Metacoq
########################################################################
: ${unicoq_CI_BRANCH:=master}
: ${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq.git}

: ${metacoq_CI_BRANCH:=master}
: ${metacoq_CI_GITURL:=https://github.com/MetaCoq/MetaCoq.git}

########################################################################
# Mathclasses + Corn
########################################################################
: ${math_classes_CI_BRANCH:=external-bignums}
: ${math_classes_CI_GITURL:=https://github.com/letouzey/math-classes.git}

: ${Corn_CI_BRANCH:=external-bignums}
: ${Corn_CI_GITURL:=https://github.com/letouzey/corn.git}

########################################################################
# Iris
########################################################################
: ${stdpp_CI_BRANCH:=master}
: ${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp.git}

: ${Iris_CI_BRANCH:=master}
: ${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/FP/iris-coq.git}

########################################################################
# HoTT
########################################################################
# Temporary overlay
: ${HoTT_CI_BRANCH:=ocaml.4.02.3}
: ${HoTT_CI_GITURL:=https://github.com/ejgallego/HoTT.git}
# : ${HoTT_CI_BRANCH:=master}
# : ${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT.git}

########################################################################
# GeoCoq
########################################################################
: ${GeoCoq_CI_BRANCH:=master}
: ${GeoCoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq.git}

########################################################################
# Flocq
########################################################################
: ${Flocq_CI_BRANCH:=master}
: ${Flocq_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/flocq/flocq.git}

########################################################################
# Coquelicot
########################################################################
: ${Coquelicot_CI_BRANCH:=master}
: ${Coquelicot_CI_GITURL:=https://scm.gforge.inria.fr/anonscm/git/coquelicot/coquelicot.git}

########################################################################
# CompCert
########################################################################
: ${CompCert_CI_BRANCH:=less_init_plugins}
: ${CompCert_CI_GITURL:=https://github.com/letouzey/CompCert.git}

########################################################################
# VST
########################################################################
: ${VST_CI_BRANCH:=master}
: ${VST_CI_GITURL:=https://github.com/Zimmi48/VST.git}

########################################################################
# fiat_parsers
########################################################################
: ${fiat_parsers_CI_BRANCH:=master}
: ${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat.git}

########################################################################
# fiat_crypto
########################################################################
: ${fiat_crypto_CI_BRANCH:=master}
: ${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto.git}

########################################################################
# formal-topology
########################################################################
: ${formal_topology_CI_BRANCH:=ci}
: ${formal_topology_CI_GITURL:=https://github.com/bmsherman/topology.git}

########################################################################
# coq-dpdgraph
########################################################################
: ${coq_dpdgraph_CI_BRANCH:=coq-trunk}
: ${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph.git}

########################################################################
# CoLoR
########################################################################
: ${Color_CI_SVNURL:=https://scm.gforge.inria.fr/anonscm/svn/color/trunk/color}

########################################################################
# SF
########################################################################
: ${sf_lf_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/lf-current/lf.tgz}
: ${sf_plf_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/plf-current/plf.tgz}
: ${sf_vfa_CI_TARURL:=https://www.cis.upenn.edu/~bcpierce/sf/vfa-current/vfa.tgz}

########################################################################
# TLC
########################################################################
: ${tlc_CI_BRANCH:=master}
: ${tlc_CI_GITURL:=https://gforge.inria.fr/git/tlc/tlc.git}

########################################################################
# Bignums
########################################################################
: ${bignums_CI_BRANCH:=master}
: ${bignums_CI_GITURL:=https://github.com/coq/bignums.git}
