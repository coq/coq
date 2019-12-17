#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

"$COQLIB"/tools/make-both-single-timing-files.py --fuzz=20 foo.v.after-timing.in foo.v.before-timing.in foo-real.v.timing.diff || exit $?

diff -u foo-real.v.timing.diff.expected foo-real.v.timing.diff || exit $?

"$COQLIB"/tools/make-both-single-timing-files.py --fuzz=20 --user foo.v.after-timing.in foo.v.before-timing.in foo-user.v.timing.diff || exit $?

diff -u foo-user.v.timing.diff.expected foo-user.v.timing.diff || exit $?
