#!/bin/bash

# Proof of concept contrib build script.

set -xe

export PATH=`pwd`/bin:$PATH

git clone --depth 3 -b mz-8.6 https://github.com/ejgallego/HoTT.git

pushd HoTT
./autogen.sh && ./configure && make -j ${NJOBS}
popd
