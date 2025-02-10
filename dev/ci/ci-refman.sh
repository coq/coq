#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

sed -i.bak doc/dune -e '/package coq-core/ d'
sed -i.bak doc/dune -e '/package rocq-core/ d'
COQRST_EXTRA=all dune build --no-buffer @refman-html
COQRST_EXTRA=all dune build --no-buffer @refman-pdf
