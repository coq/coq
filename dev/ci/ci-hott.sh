#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git_checkout mz-8.7 https://github.com/ejgallego/HoTT.git HoTT

( cd HoTT && ./autogen.sh && ./configure && make -j ${NJOBS} )
