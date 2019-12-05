#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

"$COQLIB"/tools/make-one-time-file.py time-of-build.log.in time-of-build-pretty.log || exit $?

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log || exit $?

cat time-of-build.log.in | "$COQLIB"/tools/make-one-time-file.py - time-of-build-pretty.log || exit $?

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log || exit $?

("$COQLIB"/tools/make-one-time-file.py time-of-build.log.in - || exit $?) > time-of-build-pretty.log

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log || exit $?
