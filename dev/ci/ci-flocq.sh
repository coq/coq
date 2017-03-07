#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git_checkout master https://scm.gforge.inria.fr/anonscm/git/flocq/flocq.git flocq

( cd flocq && ./autogen.sh && ./configure && ./remake -j${NJOBS} )
