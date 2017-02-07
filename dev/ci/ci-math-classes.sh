#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git clone --depth 1 -b v8.6 https://github.com/math-classes/math-classes.git
( cd math-classes && make -j ${NJOBS} && make install )

git clone --depth 1 -b v8.6 https://github.com/c-corn/corn.git
( cd corn         && make -j ${NJOBS} )

