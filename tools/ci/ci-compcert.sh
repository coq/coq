#!/bin/bash

# Proof of concept contrib build script.

set -xe

export PATH=`pwd`/bin:$PATH
ls `pwd`/bin

opam install -j ${NJOBS} -y menhir
git clone --depth 3 -b coq-8.6 https://github.com/maximedenes/CompCert.git

pushd CompCert
# Patch to avoid the upper version limit
sed -i.bak 's/8.6)/8.6|trunk)/' configure
./configure x86_32-linux && make -j ${NJOBS}
popd
