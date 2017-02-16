#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git_checkout master https://github.com/mit-plv/fiat-crypto.git fiat-crypto

( cd fiat-crypto && make -j ${NJOBS} )
