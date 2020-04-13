#!/bin/bash

set -e -x

cd $(dirname $0)/../..

dune build --display=verbose coq.install
