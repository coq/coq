#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

mkdir -p "${CI_BUILD_DIR}" && cd "${CI_BUILD_DIR}" || exit 1
wget -qO- "${sf_lf_CI_TARURL}"  | tar xvz
wget -qO- "${sf_plf_CI_TARURL}" | tar xvz
wget -qO- "${sf_vfa_CI_TARURL}" | tar xvz

( cd lf  && make clean && make )
( cd plf && make clean && make )
( cd vfa && make clean && make )
