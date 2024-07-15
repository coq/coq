#!/usr/bin/env bash

. ../template/init.sh

cd "$(dirname "${BASH_SOURCE[0]}")"

/usr/bin/env python3 -c 'import os; open("time-of-build.log", "w").write(open("time-of-build.log.in", "r").read().replace("$PWD", os.getcwd()))'

$make_one_time_file time-of-build.log time-of-build-pretty-user.log

diff -u time-of-build-pretty-user.log.expected time-of-build-pretty-user.log || exit $?

$make_one_time_file time-of-build.log time-of-build-pretty-real.log

diff -u time-of-build-pretty-real.log.expected time-of-build-pretty-real.log || exit $?
