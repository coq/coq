#!/usr/bin/env bash

. ../template/init.sh

cd "$(dirname "${BASH_SOURCE[0]}")"

$make_both_time_files time-of-build-after.log.in time-of-build-before.log.in time-of-build-both-user.log --sort-by-mem

diff -u time-of-build-both-user.log.expected time-of-build-both-user.log || exit $?

$make_both_time_files --real time-of-build-after.log.in time-of-build-before.log.in time-of-build-both-real.log --sort-by-mem

diff -u time-of-build-both-real.log.expected time-of-build-both-real.log || exit $?

for sort_kind in auto absolute diff; do
    $make_both_time_files time-of-build-after.log.in time-of-build-before.log.in time-of-build-both-user-${sort_kind}.log --sort-by-mem --sort-by=${sort_kind}

    diff -u time-of-build-both-user-${sort_kind}.log.expected time-of-build-both-user-${sort_kind}.log || exit $?

    $make_both_time_files --real time-of-build-after.log.in time-of-build-before.log.in time-of-build-both-real-${sort_kind}.log --sort-by-mem --sort-by=${sort_kind}

    diff -u time-of-build-both-real-${sort_kind}.log.expected time-of-build-both-real-${sort_kind}.log || exit $?
done
