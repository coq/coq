#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

# MetaCoq + UniCoq

git clone --depth 1 https://github.com/unicoq/unicoq.git

( cd unicoq && coq_makefile -f Make -o Makefile && make -j ${NJOBS} && make install )

git clone --depth 1 https://github.com/MetaCoq/MetaCoq.git

( cd MetaCoq && coq_makefile -f _CoqProject -o Makefile && make -j ${NJOBS} )

