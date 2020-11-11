#!/bin/sh
set -e

# Use coqc instead of coqc to work in async mode
export PATH="$BIN:$PATH"

coqc -R print-assumptions-vok/ PrintAssumptionsVOK -vos print-assumptions-vok/file1.v
coqc -R print-assumptions-vok/ PrintAssumptionsVOK -vos print-assumptions-vok/file2.v
coqc -R print-assumptions-vok/ PrintAssumptionsVOK -vok print-assumptions-vok/file2.v
