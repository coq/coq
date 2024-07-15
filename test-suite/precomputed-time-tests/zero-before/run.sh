#!/usr/bin/env bash

. ../template/init.sh

cd "$(dirname "${BASH_SOURCE[0]}")"

$make_both_time_files time-of-build-after.log.in time-of-build-before.log.in time-of-build-both.log

diff -u time-of-build-both.log.expected time-of-build-both.log || exit $?
