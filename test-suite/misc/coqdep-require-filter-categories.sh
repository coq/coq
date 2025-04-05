#!/usr/bin/env bash

set -e

cd misc/coqdep-require-filter-categories

code=0
$coqdep -worker @ROCQWORKER@ -R . 'Bla' ./*.v > stdout 2> stderr || code=$?

diff stdout.ref stdout
diff stderr.ref stderr

exit $code
