#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

sed -i.bak doc/dune 's/(package coq-core)//'
sed -i.bak doc/dune 's/(package rocq-init)//'
COQRST_EXTRA=1 dune build --no-buffer @refman-pdf
