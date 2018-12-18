#!/bin/bash

set -e -x

cd $(dirname $0)/../..

./configure -local
make -j 2 byte
make -j 2 world
