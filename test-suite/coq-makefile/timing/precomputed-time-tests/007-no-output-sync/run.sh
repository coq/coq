#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

"$COQLIB"/tools/make-one-time-file.py time-of-build.log.in time-of-build.log 2>time-of-build.err.log || exit $?

diff -u time-of-build.log.expected time-of-build.log || exit $?
diff -u time-of-build.err.log.expected time-of-build.err.log || exit $?
