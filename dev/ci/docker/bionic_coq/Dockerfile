# CACHEKEY: "bionic_coq-V2018-09-05-V1"
# ^^ Update when modifying this file.

FROM ubuntu:bionic
LABEL maintainer="e@x80.org"

ENV DEBIAN_FRONTEND="noninteractive"

RUN apt-get update -qq && apt-get install --no-install-recommends -y -qq \
        m4 automake autoconf time wget rsync git gcc-multilib opam \
        libgtk2.0-dev libgtksourceview2.0-dev \
        texlive-latex-extra texlive-fonts-recommended texlive-science tipa \
        python3-sphinx python3-pexpect python3-sphinx-rtd-theme python3-bs4 python3-sphinxcontrib.bibtex \
        python3-setuptools python3-wheel python3-pip

RUN pip3 install antlr4-python3-runtime

# Basic OPAM setup
ENV NJOBS="2" \
    OPAMROOT=/root/.opamcache \
    OPAMROOTISOK="true"

# Base opam is the set of base packages required by Coq
ENV COMPILER="4.02.3"

RUN opam init -a -y -j $NJOBS --compiler="$COMPILER" default https://opam.ocaml.org && eval $(opam config env) && opam update

# Common OPAM packages.
# `num` does not have a version number as the right version to install varies
# with the compiler version.
ENV BASE_OPAM="num ocamlfind.1.8.0 dune.1.1.1 ounit.2.0.8" \
    CI_OPAM="menhir.20180530 elpi.1.0.5 ocamlgraph.1.8.8"

# BASE switch; CI_OPAM contains Coq's CI dependencies.
ENV CAMLP5_VER="6.14" \
    COQIDE_OPAM="lablgtk.2.18.5 conf-gtksourceview.2"

RUN opam switch -y -j $NJOBS "$COMPILER" && eval $(opam config env) && \
    opam install -j $NJOBS $BASE_OPAM camlp5.$CAMLP5_VER $COQIDE_OPAM $CI_OPAM

# base+32bit switch
RUN opam switch -y -j $NJOBS "${COMPILER}+32bit" && eval $(opam config env) && \
    opam install -j $NJOBS $BASE_OPAM camlp5.$CAMLP5_VER

# EDGE switch
ENV COMPILER_EDGE="4.07.0" \
    CAMLP5_VER_EDGE="7.06" \
    COQIDE_OPAM_EDGE="lablgtk.2.18.6 conf-gtksourceview.2" \
    BASE_OPAM_EDGE="odoc.1.2.0 dune-release.0.3.0"

RUN opam switch -y -j $NJOBS $COMPILER_EDGE && eval $(opam config env) && \
    opam install -j $NJOBS $BASE_OPAM $BASE_OPAM_EDGE camlp5.$CAMLP5_VER_EDGE $COQIDE_OPAM_EDGE

# EDGE+flambda switch, we install CI_OPAM as to be able to use
# `ci-template-flambda` with everything.
RUN opam switch -y -j $NJOBS "${COMPILER_EDGE}+flambda" && eval $(opam config env) && \
    opam install -j $NJOBS $BASE_OPAM $BASE_OPAM_EDGE camlp5.$CAMLP5_VER_EDGE $COQIDE_OPAM_EDGE $CI_OPAM
