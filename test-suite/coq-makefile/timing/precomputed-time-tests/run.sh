#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"
COQLIB="$(cd ../../../.. && pwd)"
export COQLIB

./001-correct-diff-sorting-order/run.sh
./002-single-file-sorting/run.sh
