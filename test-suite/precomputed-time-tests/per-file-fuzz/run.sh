#!/usr/bin/env bash

. ../template/init.sh

cd "$(dirname "${BASH_SOURCE[0]}")"

$make_both_single_timing_files --fuzz=20 foo.v.after-timing.in foo.v.before-timing.in foo-real.v.timing.diff || exit $?

diff -u foo-real.v.timing.diff.expected foo-real.v.timing.diff || exit $?

$make_both_single_timing_files --fuzz=20 --user foo.v.after-timing.in foo.v.before-timing.in foo-user.v.timing.diff || exit $?

diff -u foo-user.v.timing.diff.expected foo-user.v.timing.diff || exit $?
