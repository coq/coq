#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

CompCert_CI_DIR=${CI_BUILD_DIR}/CompCert

opam install -j ${NJOBS} -y menhir
git_checkout ${CompCert_CI_BRANCH} ${CompCert_CI_GITURL} ${CompCert_CI_DIR}

#( cd ${CompCert_CI_DIR} && ./configure -ignore-coq-version x86_32-linux && make && make check-proof )
( cd ${CompCert_CI_DIR} && ./configure -ignore-coq-version x86_32-linux && make )
