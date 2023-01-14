#!/usr/bin/env bash

set -e

cd coqdoc-options/

coq_makefile -f _CoqProject -o Makefile

make clean

make html
