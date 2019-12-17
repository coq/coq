#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

"$COQLIB"/tools/make-one-time-file.py time-of-build.log.in time-of-build-pretty-user.log

diff -u time-of-build-pretty-user.log.expected time-of-build-pretty-user.log || exit $?

"$COQLIB"/tools/make-one-time-file.py time-of-build.log.in time-of-build-pretty-real.log

diff -u time-of-build-pretty-real.log.expected time-of-build-pretty-real.log || exit $?
