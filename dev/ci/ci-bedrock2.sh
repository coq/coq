#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

FORCE_GIT=1
git_download bedrock2

export COQEXTRAFLAGS='-native-compiler no'
( cd "${CI_BUILD_DIR}/bedrock2" && git submodule update --init --recursive && COQMF_ARGS='-arg "-async-proofs-tac-j 1"' make && make install )
