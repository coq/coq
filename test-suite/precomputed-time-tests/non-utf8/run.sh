#!/usr/bin/env bash

. ../template/init.sh

cd "$(dirname "${BASH_SOURCE[0]}")"

$make_one_time_file time-of-build.log.in time-of-build-pretty.log || exit $?

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log || exit $?

cat time-of-build.log.in | $make_one_time_file - time-of-build-pretty.log || exit $?

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log || exit $?

($make_one_time_file time-of-build.log.in - || exit $?) > time-of-build-pretty.log

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log || exit $?
