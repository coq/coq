#!/bin/sh
set -e

# Use coqc instead of $coqc to work in async mode
export PATH="$BIN:$PATH"

coqc -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vos misc/print-assumptions-vok/file1.v
coqc -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vos misc/print-assumptions-vok/file2.v
coqc -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vok misc/print-assumptions-vok/file2.v
