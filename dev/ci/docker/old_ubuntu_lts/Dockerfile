# Update CACHEKEY in the .gitlab-ci.yml when modifying this file.

FROM ubuntu:20.04
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
        zlib1g-dev zlib1g-dev:i386 \
        # Dependencies of lablgtk (for CoqIDE)
        libgtksourceview-3.0-dev adwaita-icon-theme-full \
        # Dependencies of stdlib and sphinx doc
        texlive-latex-extra texlive-fonts-recommended texlive-xetex latexmk \
        python3-pip python3-setuptools python3-pexpect python3-bs4 fonts-freefont-otf \
        # Dependency of stdlib-doc
        graphviz \
        # Dependencies of source-doc and coq-makefile
        texlive-science tipa \
        # Dependencies of HB (test suite)
        wdiff \
        # Required for fiat-crypto and Coqtail
        python-is-python3 \
      && rm -rf /var/lib/apt/lists /usr/share/doc

# More dependencies of the sphinx doc, pytest for coqtail
RUN pip3 install docutils==0.17.1 sphinx==4.5.0 sphinx_rtd_theme==1.0.0 \
        antlr4-python3-runtime==4.7.1 sphinxcontrib-bibtex==0.4.2 \
        pytest==5.4.3 \
      && rm -rf ~/.cache/pip

# We need to install OPAM 2.0 manually for now.
RUN wget https://github.com/ocaml/opam/releases/download/2.0.6/opam-2.0.6-x86_64-linux -O /usr/bin/opam && chmod 755 /usr/bin/opam

# Basic OPAM setup
ENV NJOBS="2" \
    OPAMJOBS="2" \
    OPAMROOT=/root/.opamcache \
    OPAMROOTISOK="true" \
    OPAMYES="true"

RUN mkdir -p ~/.config/dune && printf '(lang dune 2.1)\n(jobs %s)\n' $NJOBS > ~/.config/dune/config

# Base opam is the set of base packages required by Coq
ENV COMPILER="4.09.0"

# Common OPAM packages
ENV BASE_OPAM="zarith.1.11 ounit2.2.2.6 yojson.1.7.0 camlzip.1.10" \
    CI_OPAM="ocamlgraph.2.0.0 cppo.1.6.9" \
    BASE_ONLY_OPAM="dune.3.8.3 stdlib-shims.0.1.0 ocamlfind.1.8.1 odoc.2.0.2 num.1.4"

# BASE switch; CI_OPAM contains Coq's CI dependencies.
ENV COQIDE_OPAM="cairo2.0.6.1 lablgtk3-sourceview3.3.1.2"

# Must add this to COQIDE_OPAM{,_EDGE} when we update the opam
# packages "lablgtk3-gtksourceview3"

# base switch
RUN opam init -a --disable-sandboxing --compiler="$COMPILER" default https://opam.ocaml.org && eval $(opam env) && opam update && \
    opam install $BASE_OPAM $COQIDE_OPAM $CI_OPAM $BASE_ONLY_OPAM && \
    opam clean -a -c && \
    find ~ '(' -name '*.cmt' -o -name '*.cmti' ')' -delete

# base+32bit switch, note the zarith hack
RUN opam switch create "${COMPILER}+32bit" && eval $(opam env) && \
        i386 env CC='gcc -m32' opam install zarith.1.11 && \
    opam install $BASE_OPAM && \
    opam clean -a -c && \
    find ~ '(' -name '*.cmt' -o -name '*.cmti' ')' -delete

# set the locale for the benefit of Python
ENV LANG C.UTF-8
