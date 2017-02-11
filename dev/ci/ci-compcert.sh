#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

CompCert_CI_BRANCH=master
CompCert_CI_GITURL=https://github.com/AbsInt/CompCert.git

opam install -j ${NJOBS} -y menhir
git_checkout ${CompCert_CI_BRANCH} ${CompCert_CI_GITURL} CompCert

# Patch to avoid the upper version limit
( cd CompCert && sed -i.bak 's/8.6)/8.6|trunk)/' configure && ./configure x86_32-linux && make -j ${NJOBS} )
