#!/bin/bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git clone --depth 3 -b mz-8.6 https://github.com/ejgallego/HoTT.git

( cd HoTT && ./autogen.sh && ./configure && make -j ${NJOBS} )
