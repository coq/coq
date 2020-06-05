# CACHEKEY: "bionic_coq-V2020-05-24-V1"
# ^^ Update when modifying this file.

FROM ubuntu:bionic
LABEL maintainer="e@x80.org"

ENV DEBIAN_FRONTEND="noninteractive"

RUN apt-get update -qq && apt-get install --no-install-recommends -y -qq \
        # Dependencies of the image, the test-suite and external projects
        m4 automake autoconf time wget rsync git gcc-multilib build-essential unzip jq \
        # Dependencies of lablgtk (for CoqIDE)
        libgtksourceview-3.0-dev \
        # Dependencies of stdlib and sphinx doc
        texlive-latex-extra texlive-fonts-recommended texlive-xetex latexmk \
        python3-pip python3-setuptools python3-pexpect python3-bs4 fonts-freefont-otf \
        # Dependencies of source-doc and coq-makefile
        texlive-science tipa

# More dependencies of the sphinx doc
RUN pip3 install sphinx==2.3.1 sphinx_rtd_theme==0.4.3 \
                 antlr4-python3-runtime==4.7.1 sphinxcontrib-bibtex==0.4.2

# We need to install OPAM 2.0 manually for now.
RUN wget https://github.com/ocaml/opam/releases/download/2.0.6/opam-2.0.6-x86_64-linux -O /usr/bin/opam && chmod 755 /usr/bin/opam

# Basic OPAM setup
ENV NJOBS="2" \
    OPAMJOBS="2" \
    OPAMROOT=/root/.opamcache \
    OPAMROOTISOK="true" \
    OPAMYES="true"

# Base opam is the set of base packages required by Coq
ENV COMPILER="4.05.0"

# Common OPAM packages.
# `num` does not have a version number as the right version to install varies
# with the compiler version.
ENV BASE_OPAM="num ocamlfind.1.8.1 ounit.2.2.2 odoc.1.5.0" \
    CI_OPAM="menhir.20190626 ocamlgraph.1.8.8" \
    BASE_ONLY_OPAM="elpi.1.11.0"

# BASE switch; CI_OPAM contains Coq's CI dependencies.
ENV COQIDE_OPAM="cairo2.0.6.1 lablgtk3-sourceview3.3.1.0"

# Must add this to COQIDE_OPAM{,_EDGE} when we update the opam
# packages "lablgtk3-gtksourceview3"

# base switch
RUN opam init -a --disable-sandboxing --compiler="$COMPILER" default https://opam.ocaml.org && eval $(opam env) && opam update && \
    opam install $BASE_OPAM $COQIDE_OPAM $CI_OPAM $BASE_ONLY_OPAM

# base+32bit switch
RUN opam switch create "${COMPILER}+32bit" && eval $(opam env) && \
    opam install $BASE_OPAM

# EDGE switch
ENV COMPILER_EDGE="4.10.0" \
    BASE_OPAM_EDGE="dune.2.5.1 dune-release.1.3.3 ocamlformat.0.14.2"

# EDGE+flambda switch, we install CI_OPAM as to be able to use
# `ci-template-flambda` with everything.
RUN opam switch create "${COMPILER_EDGE}+flambda" && eval $(opam env) && \
    opam install $BASE_OPAM $BASE_OPAM_EDGE $COQIDE_OPAM $CI_OPAM

RUN opam clean -a -c
