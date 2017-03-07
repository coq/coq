#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

install_ssreflect

# Setup coquelicot
git_checkout master https://scm.gforge.inria.fr/anonscm/git/coquelicot/coquelicot.git coquelicot

( cd coquelicot && ./autogen.sh && ./configure && ./remake -j${NJOBS} )
