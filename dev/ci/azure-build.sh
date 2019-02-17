#!/bin/bash

set -e -x

cd $(dirname $0)/../..

make -f Makefile.dune coq coqide-server
