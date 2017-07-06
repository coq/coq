#!/usr/bin/env bash

set -ex

source dev/ci/exports.sh

fold-start "Configuring..." "coq.config"
./configure -prefix "$CI_INSTALL" -native-compiler ${NATIVE_COMP} ${EXTRA_CONF}
fold-end "Configuration done." "coq.config"

fold-start "Building..." "coq.build"
make -j ${NJOBS}
fold-end "Build done." "coq.build"

fold-start "Installing..." "coq.install"
make install
cp bin/fake_ide "$CI_INSTALL"/bin
fold-end "Installation done." "coq.install"

save-artifact-coq
