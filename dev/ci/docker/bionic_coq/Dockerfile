# CACHEKEY: "bionic_coq-v8.8-V2018-07-06"
# ^^ Update when modifying this file.

FROM ubuntu:bionic
LABEL maintainer="e@x80.org"

ENV DEBIAN_FRONTEND="noninteractive"

RUN apt-get update -qq && apt-get install --no-install-recommends -y -qq \
        m4 automake autoconf time wget rsync git gcc-multilib opam \
        libgtk2.0-dev libgtksourceview2.0-dev \
        texlive-latex-extra texlive-fonts-recommended texlive-science tipa hevea \
        python3-sphinx python3-pexpect python3-sphinx-rtd-theme python3-bs4 python3-sphinxcontrib.bibtex \
        python3-setuptools python3-wheel python3-pip

RUN pip3 install antlr4-python3-runtime

# Basic OPAM setup
ENV NJOBS="2" \
    OPAMROOT=/root/.opamcache \
    OPAMROOTISOK="true"

# Base opam is the set of base packages required by Coq
ENV COMPILER="4.02.3" \
    BASE_OPAM="num ocamlfind"

RUN opam init -a -y -j $NJOBS --compiler="$COMPILER" default https://opam.ocaml.org && eval $(opam config env) && opam update

# Setup of the base switch; CI_OPAM contains Coq's CI dependencies.
ENV CAMLP5_VER="6.14" \
    COQIDE_OPAM="lablgtk.2.18.5 conf-gtksourceview.2" \
    CI_OPAM="menhir ppx_tools_versioned ppx_deriving ocaml-migrate-parsetree ocamlgraph"

RUN opam switch -y -j $NJOBS "$COMPILER" && eval $(opam config env) && \
    opam install -j $NJOBS $BASE_OPAM camlp5.$CAMLP5_VER $COQIDE_OPAM $CI_OPAM

# base+32bit switch
RUN opam switch -y -j $NJOBS "${COMPILER}+32bit" && eval $(opam config env) && \
    opam install -j $NJOBS $BASE_OPAM camlp5.$CAMLP5_VER

# BE switch
ENV COMPILER_BE="4.06.1" \
    CAMLP5_VER_BE="7.05" \
    COQIDE_OPAM_BE="lablgtk.2.18.6 conf-gtksourceview.2"

RUN opam switch -y -j $NJOBS $COMPILER_BE && eval $(opam config env) && \
    opam install -j $NJOBS $BASE_OPAM camlp5.$CAMLP5_VER_BE $COQIDE_OPAM_BE

# BE+flambda switch
RUN opam switch -y -j $NJOBS "${COMPILER_BE}+flambda" && eval $(opam config env) && \
    opam install -j $NJOBS $BASE_OPAM camlp5.$CAMLP5_VER_BE $COQIDE_OPAM_BE $CI_OPAM
