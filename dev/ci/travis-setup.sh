#!/usr/bin/env bash

# setup travis only things

set -ex

opam init -j ${NJOBS} --compiler=${COMPILER} -n -y
