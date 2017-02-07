#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git_checkout v8.6 https://github.com/math-classes/math-classes.git math-classes
( cd math-classes && make -j ${NJOBS} && make install )

git_checkout v8.6 https://github.com/c-corn/corn.git corn
( cd corn         && make -j ${NJOBS} )

