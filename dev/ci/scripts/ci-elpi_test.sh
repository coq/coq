#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/elpi"
  dune build --root  . --only-packages=rocq-elpi-tests,rocq-elpi-tests-stdlib @all
)
