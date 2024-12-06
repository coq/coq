#!/usr/bin/env bash

set -e

$coqc misc/PStringExtraction.v > misc/PStringExtraction.real 2>&1

if [[ "$(ocamlc -config-var word_size)" = "64" ]]; then
  diff -u misc/PStringExtraction.out misc/PStringExtraction.real
fi
