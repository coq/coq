#!/usr/bin/env bash

# Use this script to preserve the exit code of $1 when piping it to
# `tee $2`.  We have a separate script, because this only works in
# bash, which we don't require project-wide.

"$1" 2>&1 | tee "$2"
exit ${PIPESTATUS[0]}
