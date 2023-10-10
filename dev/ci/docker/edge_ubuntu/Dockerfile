# Update CACHEKEY in the .gitlab-ci.yml when modifying this file.

FROM ubuntu:23.04
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
        libgtksourceview-3.0-dev adwaita-icon-theme-full \
        # Dependencies of source-doc and coq-makefile
        texlive-latex-extra texlive-science tipa \
        # Dependencies of HB (test suite)
        wdiff \
        # Required to get the wget step to succeed
        ca-certificates \
        # Required for fiat-crypto and Coqtail
        python-is-python3 \
      && rm -rf /var/lib/apt/lists /usr/share/doc

# We need to install OPAM 2.0 manually for now.
RUN wget https://github.com/ocaml/opam/releases/download/2.1.5/opam-2.1.5-x86_64-linux -O /usr/bin/opam && chmod 755 /usr/bin/opam

# Basic OPAM setup
ENV NJOBS="2" \
    OPAMJOBS="2" \
    OPAMROOT=/root/.opamcache \
    OPAMROOTISOK="true" \
    OPAMYES="true"

# Edge opam is the set of edge packages required by Coq
#
# Note: no ppxlib on 5.2.0+trunk , also odoc is broken, thus we need
# to remove dune-release
ENV COMPILER="5.2.0+trunk" \
    BASE_OPAM="zarith.1.13 ounit2.2.2.6" \
    CI_OPAM="ocamlgraph.2.0.0 cppo.1.6.9" \
    BASE_OPAM_EDGE="dune.3.12.1 dune-build-info.3.12.1 ocamlfind.1.9.6" \
    CI_OPAM_EDGE="" \
    COQIDE_OPAM_EDGE="lablgtk3-sourceview3.3.1.3"

# EDGE+flambda switch, we install CI_OPAM as to be able to use
# `ci-template-flambda` with everything.
RUN opam init -a --disable-sandboxing --bare && eval $(opam env) && opam update && \
    opam switch create "${COMPILER}+flambda" \
      --packages="ocaml-variants.${COMPILER},ocaml-option-flambda" && eval $(opam env) && \
    opam install $BASE_OPAM $BASE_OPAM_EDGE $COQIDE_OPAM_EDGE $CI_OPAM $CI_OPAM_EDGE && \
    opam clean -a -c && \
    find ~ '(' -name '*.cmt' -o -name '*.cmti' ')' -delete

# set the locale for the benefit of Python
ENV LANG C.UTF-8
