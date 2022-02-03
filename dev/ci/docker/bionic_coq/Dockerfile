# Update CACHEKEY in the .gitlab-ci.yml when modifying this file.

FROM ubuntu:bionic
LABEL maintainer="e@x80.org"

ENV DEBIAN_FRONTEND="noninteractive"

# We need libgmp-dev:i386 for zarith; maybe we could also install GTK
RUN dpkg --add-architecture i386

RUN apt-get update -qq && apt-get install --no-install-recommends -y -qq \
        # Dependencies of the image, the test-suite and external projects
        m4 automake autoconf time wget rsync git gcc-multilib build-essential unzip jq \
        # Dependencies of ZArith
        perl libgmp-dev libgmp-dev:i386 \
        # Dependencies of lablgtk (for CoqIDE)
        libgtksourceview-3.0-dev \
        # Dependencies of Gappa
        libboost1.65-all-dev libmpfr-dev autoconf-archive bison flex \
        # Dependencies of stdlib and sphinx doc
        texlive-latex-extra texlive-fonts-recommended texlive-xetex latexmk \
        python3-pip python3-setuptools python3-pexpect python3-bs4 fonts-freefont-otf \
        # Dependencies of source-doc and coq-makefile
        texlive-science tipa

# More dependencies of the sphinx doc, pytest for coqtail
RUN pip3 install docutils==0.16 sphinx==3.0.2 sphinx_rtd_theme==0.4.3 \
        antlr4-python3-runtime==4.7.1 sphinxcontrib-bibtex==0.4.2 \
        pytest==5.4.3

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

# Common OPAM packages
ENV BASE_OPAM="zarith.1.12 ocamlfind.1.9.1 ounit2.2.2.3 odoc.1.5.3" \
    CI_OPAM="ocamlgraph.1.8.8 yojson.1.7.0 cppo.1.6.8" \
    BASE_ONLY_OPAM="dune.2.7.1 elpi.1.13.8 stdlib-shims.0.1.0"

# BASE switch; CI_OPAM contains Coq's CI dependencies.
ENV COQIDE_OPAM="cairo2.0.6.1 lablgtk3-sourceview3.3.1.0"

# Must add this to COQIDE_OPAM{,_EDGE} when we update the opam
# packages "lablgtk3-gtksourceview3"

# base switch
RUN opam init -a --disable-sandboxing --compiler="$COMPILER" default https://opam.ocaml.org && eval $(opam env) && opam update && \
    opam install $BASE_OPAM $COQIDE_OPAM $CI_OPAM $BASE_ONLY_OPAM

# base+32bit switch, note the zarith hack
RUN opam switch create "${COMPILER}+32bit" && eval $(opam env) && \
        i386 env CC='gcc -m32' opam install zarith.1.12 && \
        opam install $BASE_OPAM

# EDGE switch, dune 2.8 is required for OCaml 4.12
ENV COMPILER_EDGE="4.13.0" \
    BASE_OPAM_EDGE="dune.2.9.1 dune-release.1.5.0"

# EDGE+flambda switch, we install CI_OPAM as to be able to use
# `ci-template-flambda` with everything.
RUN opam switch create "${COMPILER_EDGE}+flambda" \
      --repositories default,ocaml-beta=git+https://github.com/ocaml/ocaml-beta-repository.git \
      --packages="ocaml-variants.${COMPILER_EDGE}+options,ocaml-option-flambda" && eval $(opam env) && \
    opam install $BASE_OPAM $BASE_OPAM_EDGE $COQIDE_OPAM $CI_OPAM

RUN opam clean -a -c

# set the locale for the benefit of Python
ENV LANG C.UTF-8
