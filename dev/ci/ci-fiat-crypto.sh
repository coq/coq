#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git clone --depth 3 https://github.com/mit-plv/fiat-crypto.git

( cd fiat-crypto && make -j ${NJOBS} )

# ( cd corn && make -j ${NJOBS} )

