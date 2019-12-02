#!/usr/bin/env bash

set -x
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

python2 "$COQLIB"/tools/make-both-single-timing-files.py --fuzz=20 fooafter.timing foobefore.timing foo.out.log2 || exit $?
python3 "$COQLIB"/tools/make-both-single-timing-files.py --fuzz=20 fooafter.timing foobefore.timing foo.out.log3 || exit $?

diff -u foo.out.expected foo.out.log2 || exit $?
diff -u foo.out.expected foo.out.log3 || exit $?
