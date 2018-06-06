#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

CompCert_CI_DIR="${CI_BUILD_DIR}/CompCert"

# Temporal workaround, to be removed when upstream decides what to do
# with their problem.
opam install -y menhir.20180528

git_checkout "${CompCert_CI_BRANCH}" "${CompCert_CI_GITURL}" "${CompCert_CI_DIR}"

( cd "${CompCert_CI_DIR}" && ./configure -ignore-coq-version x86_32-linux && make && make check-proof )
