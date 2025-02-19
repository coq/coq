#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download struct_tact
git_download inf_seq_ext
git_download cheerios
git_download verdi
git_download verdi_raft

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/struct_tact"
  make
  make install
)

( cd "${CI_BUILD_DIR}/inf_seq_ext"
  make
  make install
)

( cd "${CI_BUILD_DIR}/cheerios"
  make
  make install
)

( cd "${CI_BUILD_DIR}/verdi"
  make
  make install
)

( cd "${CI_BUILD_DIR}/verdi_raft"
  make
)
