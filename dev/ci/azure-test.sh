#!/bin/bash

set -e -x

#NB: if we make test-suite from the main makefile we get environment
#too large for exec error
cd $(dirname $0)/../../
make -f Makefile.dune test-suite
