#!/usr/bin/env bash

set -ex

source dev/ci/exports.sh

fold-start "Configuring..." "coq.config"
./configure -local -native-compiler ${NATIVE_COMP} ${EXTRA_CONF}
fold-end "Configuration done." "coq.config"

fold-start "Building..." "coq.build"
make -j ${NJOBS} coqocaml
fold-end "Build done." "coq.build"
