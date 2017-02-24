#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

fiat_parsers_CI_BRANCH=master
fiat_parsers_CI_GITURL=https://github.com/mit-plv/fiat.git

git_checkout ${fiat_parsers_CI_BRANCH} ${fiat_parsers_CI_GITURL} fiat

( cd fiat && make -j ${NJOBS} parsers )
