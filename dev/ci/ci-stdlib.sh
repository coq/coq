#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "stdlib"
  dev/with-rocq-wrap.sh dune build --root . --only-packages=rocq-stdlib @install
  dev/with-rocq-wrap.sh dune install --root . rocq-stdlib --prefix="$CI_INSTALL_DIR"
)
