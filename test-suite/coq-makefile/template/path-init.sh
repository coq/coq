#!/bin/sh
set -e
set -o pipefail

export PATH="$COQBIN:$PATH"
export LC_ALL=C
if which cygpath >/dev/null 2>&1; then OCAMLFINDSEP=\;; else OCAMLFINDSEP=:; fi
export OCAMLPATH=$PWD/_test$OCAMLFINDSEP$OCAMLPATH
