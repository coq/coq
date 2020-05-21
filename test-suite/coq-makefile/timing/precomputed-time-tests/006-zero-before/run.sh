#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

"$COQLIB"/tools/make-both-time-files.py time-of-build-after.log.in time-of-build-before.log.in time-of-build-both.log

diff -u time-of-build-both.log.expected time-of-build-both.log || exit $?
