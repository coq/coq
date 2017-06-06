#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

wget http://adam.chlipala.net/cpdt/cpdt.tgz
tar xvfz cpdt.tgz

( cd cpdt && make clean && (make TIMED=1 2>&1 | tee time-of-build.log; exit ${PIPESTATUS[0]}) && make -f Makefile.coq print-pretty-timed )
