# Update CACHEKEY in the .gitlab-ci.yml when modifying this file.

FROM ubuntu:24.04
LABEL maintainer="e@x80.org"

ENV DEBIAN_FRONTEND="noninteractive"

# We need libgmp-dev:i386 for zarith; maybe we could also install GTK
RUN dpkg --add-architecture i386

RUN apt-get update -qq && apt-get install --no-install-recommends -y -qq \
        # Dependencies of the image, the test-suite and external projects
        m4 automake autoconf time wget rsync git gcc-multilib build-essential unzip jq \
        # Dependencies of ZArith
        perl libgmp-dev libgmp-dev:i386 \
        # Dependencies of devtools
        zlib1g-dev \
        # Dependencies of lablgtk (for CoqIDE)
        libgtksourceview-3.0-dev adwaita-icon-theme-full \
        # Dependencies of stdlib and sphinx doc
        texlive-latex-extra texlive-fonts-recommended texlive-xetex latexmk \
        python3-pip python3-setuptools python3-pexpect python3-bs4 fonts-freefont-otf \
        # pipeline-stats
        python3-gitlab python3-tabulate \
        # Dependencies of source-doc and coq-makefile
        texlive-latex-extra texlive-science tipa \
        # Dependencies of HB (test suite)
        wdiff \
        # Required to get the wget step to succeed
        ca-certificates \
        # Required for fiat-crypto and Coqtail
        python-is-python3 \
      && rm -rf /var/lib/apt/lists /usr/share/doc

# More dependencies of the sphinx doc
RUN pip3 install --break-system-packages docutils==0.17.1 sphinx==5.3.0 sphinx_rtd_theme==1.0.0 \
        antlr4-python3-runtime==4.7.1 sphinxcontrib-bibtex==2.5.0 \
      && rm -rf ~/.cache/pip

# We need to install OPAM 2.0 manually for now.
RUN wget https://github.com/ocaml/opam/releases/download/2.1.5/opam-2.1.5-x86_64-linux -O /usr/bin/opam && chmod 755 /usr/bin/opam

# Basic OPAM setup
ENV NJOBS="2" \
    OPAMJOBS="2" \
    OPAMROOT=/root/.opamcache \
    OPAMROOTISOK="true" \
    OPAMYES="true"

RUN mkdir -p ~/.config/dune && printf '(lang dune 2.1)\n(jobs %s)\n' $NJOBS > ~/.config/dune/config

# Edge opam is the set of edge packages required by Coq
ENV COMPILER="4.14.1" \
    BASE_OPAM="zarith.1.13 ounit2.2.2.6 camlzip.1.13" \
    CI_OPAM="ocamlgraph.2.0.0 cppo.1.6.9" \
    BASE_OPAM_EDGE="dune.3.14.0 dune-build-info.3.14.0 dune-release.2.0.0 ocamlfind.1.9.6 odoc.2.3.1" \
    CI_OPAM_EDGE="elpi.2.0.7 ppx_import.1.10.0 cmdliner.1.1.1 sexplib.v0.15.1 ppx_sexp_conv.v0.15.1 ppx_hash.v0.15.0 ppx_compare.v0.15.0 ppx_deriving_yojson.3.7.0 yojson.2.1.0 uri.4.2.0 ppx_yojson_conv.v0.15.1 ppx_inline_test.v0.15.1 ppx_assert.v0.15.0 ppx_optcomp.v0.15.0 lsp.1.16.2 sel.0.6.0" \
    COQIDE_OPAM_EDGE="lablgtk3-sourceview3.3.1.3"

# EDGE+flambda switch, we install CI_OPAM as to be able to use
# `ci-template-flambda` with everything.
RUN opam init -a --disable-sandboxing --bare && eval $(opam env) && opam update && \
    opam switch create "${COMPILER}+flambda" \
      --repositories default,ocaml-beta=git+https://github.com/ocaml/ocaml-beta-repository.git,coq-core-dev=https://coq.inria.fr/opam/core-dev \
      --packages="ocaml-variants.${COMPILER}+options,ocaml-option-flambda" && eval $(opam env) && \
    opam install $BASE_OPAM $BASE_OPAM_EDGE $COQIDE_OPAM_EDGE $CI_OPAM $CI_OPAM_EDGE && \
    opam clean -a -c

# set the locale for the benefit of Python
ENV LANG C.UTF-8
