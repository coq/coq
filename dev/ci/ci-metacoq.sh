#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

# MetaCoq + UniCoq

git_checkout master https://github.com/unicoq/unicoq.git unicoq

( cd unicoq && coq_makefile -f Make -o Makefile && make -j ${NJOBS} && make install )

git_checkout master https://github.com/MetaCoq/MetaCoq.git MetaCoq

( cd MetaCoq && coq_makefile -f _CoqProject -o Makefile && make -j ${NJOBS} )

