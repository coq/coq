#!/bin/sh
set -e
set -o pipefail

export PATH="$COQBIN:$PATH"
export LC_ALL=C
export OCAMLPATH=$PWD/_test:$OCAMLPATH
