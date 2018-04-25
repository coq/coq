#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

unicoq_CI_DIR=${CI_BUILD_DIR}/unicoq
mtac2_CI_DIR=${CI_BUILD_DIR}/Mtac2

# Setup UniCoq

git_checkout "${unicoq_CI_BRANCH}" "${unicoq_CI_GITURL}" "${unicoq_CI_DIR}"

( cd "${unicoq_CI_DIR}" && coq_makefile -f Make -o Makefile && make && make install )

# Setup MetaCoq

git_checkout "${mtac2_CI_BRANCH}" "${mtac2_CI_GITURL}" "${mtac2_CI_DIR}"

( cd "${mtac2_CI_DIR}" && coq_makefile -f _CoqProject -o Makefile && make )
