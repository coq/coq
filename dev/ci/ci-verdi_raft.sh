#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download struct_tact

( cd "${CI_BUILD_DIR}/struct_tact" && ./configure && make && make install )

git_download inf_seq_ext

( cd "${CI_BUILD_DIR}/inf_seq_ext" && ./configure && make && make install )

git_download cheerios

( cd "${CI_BUILD_DIR}/cheerios" && ./configure && make && make install )

git_download verdi

( cd "${CI_BUILD_DIR}/verdi" && ./configure && make && make install )

git_download verdi_raft

( cd "${CI_BUILD_DIR}/verdi_raft" && ./configure && make )
