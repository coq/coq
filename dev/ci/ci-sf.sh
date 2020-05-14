#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download sf

( cd lf-current  && make clean && make )
( cd plf-current && make clean && make )
( cd vfa-current && make clean && make )
# ( cd qc-current && make clean && make )
