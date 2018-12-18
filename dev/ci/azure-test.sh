#!/bin/bash

set -e -x

#NB: if we make test-suite from the main makefile we get environment
#too large for exec error
cd $(dirname $0)/../../test-suite
make -j 2 clean
make -j 2 PRINT_LOGS=1
