#!/usr/bin/env bash

. ../template/init.sh

cd "$(dirname "${BASH_SOURCE[0]}")"

$make_one_time_file time-of-build.log.in time-of-build.log 2>time-of-build.err.log || exit $?

diff -u time-of-build.log.expected time-of-build.log || exit $?
diff -u time-of-build.err.log.expected time-of-build.err.log || exit $?
