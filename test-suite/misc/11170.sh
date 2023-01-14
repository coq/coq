#!/usr/bin/env bash

set -e

export OCAMLRUNPARAM=s=1

coqc aux11170.v
