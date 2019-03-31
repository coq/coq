#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

python2 "$COQLIB"/tools/make-one-time-file.py time-of-build.log.in time-of-build-pretty.log2 || exit $?
python3 "$COQLIB"/tools/make-one-time-file.py time-of-build.log.in time-of-build-pretty.log3 || exit $?

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log2 || exit $?
diff -u time-of-build-pretty.log.expected time-of-build-pretty.log3 || exit $?

cat time-of-build.log.in | python2 "$COQLIB"/tools/make-one-time-file.py - time-of-build-pretty.log2 || exit $?
cat time-of-build.log.in | python3 "$COQLIB"/tools/make-one-time-file.py - time-of-build-pretty.log3 || exit $?

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log2 || exit $?
diff -u time-of-build-pretty.log.expected time-of-build-pretty.log3 || exit $?

(python2 "$COQLIB"/tools/make-one-time-file.py time-of-build.log.in - || exit $?) > time-of-build-pretty.log2
(python3 "$COQLIB"/tools/make-one-time-file.py time-of-build.log.in - || exit $?) > time-of-build-pretty.log3

diff -u time-of-build-pretty.log.expected time-of-build-pretty.log2 || exit $?
diff -u time-of-build-pretty.log.expected time-of-build-pretty.log3 || exit $?
