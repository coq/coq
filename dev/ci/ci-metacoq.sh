#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

unicoq_CI_DIR=${CI_BUILD_DIR}/unicoq
metacoq_CI_DIR=${CI_BUILD_DIR}/MetaCoq

# Setup UniCoq

git_checkout "${unicoq_CI_BRANCH}" "${unicoq_CI_GITURL}" "${unicoq_CI_DIR}"

( cd "${unicoq_CI_DIR}" && coq_makefile -f Make -o Makefile && make && make install )

# Setup MetaCoq

git_checkout "${metacoq_CI_BRANCH}" "${metacoq_CI_GITURL}" "${metacoq_CI_DIR}"

( cd "${metacoq_CI_DIR}" && coq_makefile -f _CoqProject -o Makefile && make )
