#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git clone --depth 3 https://scm.gforge.inria.fr/anonscm/git/flocq/flocq.git

( cd flocq && ./autogen.sh && ./configure && ./remake -j${NJOBS} )
