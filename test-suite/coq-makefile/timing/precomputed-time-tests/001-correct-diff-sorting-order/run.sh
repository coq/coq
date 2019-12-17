#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

"$COQLIB"/tools/make-both-time-files.py time-of-build-after.log.in time-of-build-before.log.in time-of-build-both-user.log

diff -u time-of-build-both-user.log.expected time-of-build-both-user.log || exit $?

"$COQLIB"/tools/make-both-time-files.py --real time-of-build-after.log.in time-of-build-before.log.in time-of-build-both-real.log

diff -u time-of-build-both-real.log.expected time-of-build-both-real.log || exit $?
