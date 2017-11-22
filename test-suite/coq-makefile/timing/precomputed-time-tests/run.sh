#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"
export COQLIB="$(cd ../../../.. && pwd)"

./001-correct-diff-sorting-order/run.sh || exit $?
./002-single-file-sorting/run.sh || exit $?
