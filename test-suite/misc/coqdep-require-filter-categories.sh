#!/usr/bin/env bash

set -e

cd misc/coqdep-require-filter-categories

code=0
$coqdep -worker @ROCQWORKER@ -R . 'Bla' ./*.v -w module-not-found > stdout 2> stderr || code=$?

diff -u stdout.ref stdout
diff -u stderr.ref stderr

exit $code
