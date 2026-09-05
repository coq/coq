#!/usr/bin/env bash

# Check that rocq dep does not look for Require or sentence ends inside
# string literals (#22442).

set -e

cd misc/coqdep-string-literals

code=0
$coqdep -worker @ROCQWORKER@ -R . 'Test' ./*.v > stdout 2> stderr || code=$?

diff -u stdout.ref stdout
diff -u stderr.ref stderr

exit $code
