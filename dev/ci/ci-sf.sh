#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download sf

( cd lf-current && make )
( cd plf-current && make )
( cd vfa-current && make )
# ( cd qc-current && make clean && make )
