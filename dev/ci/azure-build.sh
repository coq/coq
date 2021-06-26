#!/bin/bash

set -e -x

cd $(dirname $0)/../..

eval $(opam env)
make -f Makefile.dune world
