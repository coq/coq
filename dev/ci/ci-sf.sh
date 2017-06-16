#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

# XXX: Needs fixing to properly set the build directory.
wget ${sf_CI_TARURL}
tar xvfz sf.tgz

( cd sf && sed -i.bak 's/(K,N)/((K,N))/' LibTactics.v && make clean && make )


