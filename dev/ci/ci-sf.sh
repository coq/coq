#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

mkdir -p ${CI_BUILD_DIR} && cd ${CI_BUILD_DIR}
wget -qO- ${sf_lf_CI_TARURL}  | tar xvz
wget -qO- ${sf_plf_CI_TARURL} | tar xvz
wget -qO- ${sf_vfa_CI_TARURL} | tar xvz

sed -i.bak '1i From Coq Require Extraction.' lf/Extraction.v
sed -i.bak '1i From Coq Require Extraction.' vfa/Extract.v

( cd lf && make clean && make )

( cd plf && sed -i.bak 's/(K,N)/((K,N))/' LibTactics.v && make clean && make )

( cd vfa && make clean && make )
