#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

opam install -j ${NJOBS} -y menhir
git clone --depth 3 -b coq-8.6 https://github.com/maximedenes/CompCert.git

# Patch to avoid the upper version limit
( cd CompCert && sed -i.bak 's/8.6)/8.6|trunk)/' configure && ./configure x86_32-linux && make -j ${NJOBS} )
