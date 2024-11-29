#!/usr/bin/env bash

set -e

code=0
$coqc misc/PStringExtraction.v > misc/PStringExtraction.real 2>&1 || code=$?

if [ $code != 0 ]; then
  cat misc/PStringExtraction.real
  exit $code
fi

if [[ "$(ocamlc -config-var word_size)" = "64" ]]; then
  diff -u misc/PStringExtraction.out misc/PStringExtraction.real
fi
