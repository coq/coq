# CACHEKEY: "bionic_coq-v8.9-V2018-10-22"
# ^^ Update when modifying this file.

FROM ubuntu:bionic
LABEL maintainer="e@x80.org"

ENV DEBIAN_FRONTEND="noninteractive"

RUN apt-get update -qq && apt-get install --no-install-recommends -y -qq \
        # Dependencies of the image, the test-suite and external projects
        m4 automake autoconf time wget rsync git gcc-multilib build-essential unzip \
        # Dependencies of lablgtk (for CoqIDE)
        libgtk2.0-dev libgtksourceview2.0-dev \
        # Dependencies of stdlib and sphinx doc
        texlive-latex-extra texlive-fonts-recommended texlive-xetex latexmk \
        xindy python3-pip python3-setuptools python3-pexpect python3-bs4 \
        python3-sphinx python3-sphinx-rtd-theme python3-sphinxcontrib.bibtex \
        # Dependencies of source-doc and coq-makefile
        texlive-science tipa

# More dependencies of the sphinx doc
RUN pip3 install antlr4-python3-runtime

# We need to install OPAM 2.0 manually for now.
RUN wget https://github.com/ocaml/opam/releases/download/2.0.0/opam-2.0.0-x86_64-linux -O /usr/bin/opam && chmod 755 /usr/bin/opam

# Basic OPAM setup
ENV NJOBS="2" \
    OPAMJOBS="2" \
    OPAMROOT=/root/.opamcache \
    OPAMROOTISOK="true" \
    OPAMYES="true"

# Base opam is the set of base packages required by Coq
ENV COMPILER="4.02.3"

# Common OPAM packages.
# `num` does not have a version number as the right version to install varies
# with the compiler version.
ENV BASE_OPAM="num ocamlfind.1.8.0 dune.1.1.1 ounit.2.0.8" \
    CI_OPAM="menhir.20180530 elpi.1.1.0 ocamlgraph.1.8.8"

# BASE switch; CI_OPAM contains Coq's CI dependencies.
ENV CAMLP5_VER="6.14" \
    COQIDE_OPAM="lablgtk.2.18.5 conf-gtksourceview.2"

# The separate `opam install ocamlfind` workarounds an OPAM repository bug in 4.02.3
RUN opam init -a --disable-sandboxing --compiler="$COMPILER" default https://opam.ocaml.org && eval $(opam env) && opam update && \
    opam install ocamlfind.1.8.0 && \
    opam install $BASE_OPAM camlp5.$CAMLP5_VER $COQIDE_OPAM $CI_OPAM

# base+32bit switch
RUN opam switch create "${COMPILER}+32bit" && eval $(opam env) && \
    opam install ocamlfind.1.8.0 && \
    opam install $BASE_OPAM camlp5.$CAMLP5_VER

# EDGE switch
ENV COMPILER_EDGE="4.07.0" \
    CAMLP5_VER_EDGE="7.06" \
    COQIDE_OPAM_EDGE="lablgtk.2.18.6 conf-gtksourceview.2"

RUN opam switch create $COMPILER_EDGE && eval $(opam env) && \
    opam install $BASE_OPAM $BASE_OPAM_EDGE camlp5.$CAMLP5_VER_EDGE $COQIDE_OPAM_EDGE

# EDGE+flambda switch, we install CI_OPAM as to be able to use
# `ci-template-flambda` with everything.
RUN opam switch create "${COMPILER_EDGE}+flambda" && eval $(opam env) && \
    opam install $BASE_OPAM $BASE_OPAM_EDGE camlp5.$CAMLP5_VER_EDGE $COQIDE_OPAM_EDGE $CI_OPAM

RUN opam clean -a -c
