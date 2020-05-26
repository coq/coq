#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"
COQLIB="$(cd ../../../.. && pwd)"
export COQLIB

./001-correct-diff-sorting-order/run.sh
./002-single-file-sorting/run.sh
./003-non-utf8/run.sh
./004-per-file-fuzz/run.sh
./005-correct-diff-sorting-order-mem/run.sh
./006-zero-before/run.sh
