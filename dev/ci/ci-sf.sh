#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

CIRCLE_SF_TOKEN=00127070c10f5f09574b050e4f08e924764680d2
data=$(wget https://circleci.com/api/v1.1/project/gh/DeepSpec/sfdev/latest/artifacts?circle-token=${CIRCLE_SF_TOKEN} -O -)

mkdir -p "${CI_BUILD_DIR}" && cd "${CI_BUILD_DIR}"

sf_lf_CI_TARURL=$(echo "$data"  | jq -rc '.[] | select (.path == "lf.tgz") | .url')
sf_plf_CI_TARURL=$(echo "$data" | jq -rc '.[] | select (.path == "plf.tgz") | .url')
sf_vfa_CI_TARURL=$(echo "$data" | jq -rc '.[] | select (.path == "vfa.tgz") | .url')

wget -O - "${sf_lf_CI_TARURL}" | tar xvz
wget -O - "${sf_plf_CI_TARURL}" | tar xvz
wget -O - "${sf_vfa_CI_TARURL}" | tar xvz

( cd lf  && make clean && make )
( cd plf && make clean && make )
( cd vfa && make clean && make )
