#!/bin/sh
set -e

# Use rocq c instead of $coqc to work in async mode
export PATH="$BIN:$PATH"

rocq c -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vos misc/print-assumptions-vok/file1.v
rocq c -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vos misc/print-assumptions-vok/file2.v
rocq c -R misc/print-assumptions-vok/ PrintAssumptionsVOK -vok misc/print-assumptions-vok/file2.v
