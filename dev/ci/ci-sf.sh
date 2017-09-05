#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

# XXX: Needs fixing to properly set the build directory.
wget ${sf_lf_CI_TARURL}
wget ${sf_plf_CI_TARURL}
wget ${sf_vfa_CI_TARURL}
tar xvfz lf.tgz
tar xvfz plf.tgz
tar xvfz vfa.tgz

sed -i.bak '1i From Coq Require Extraction.' lf/Extraction.v
sed -i.bak '1i From Coq Require Extraction.' vfa/Extract.v

( cd lf && make clean && make )

( cd plf && sed -i.bak 's/(K,N)/((K,N))/' LibTactics.v && make clean && make )

( cd vfa && make clean && make )
