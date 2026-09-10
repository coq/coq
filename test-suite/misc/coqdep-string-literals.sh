#!/usr/bin/env bash

# Check that rocq dep does not look for Require or sentence ends inside
# string literals (#22442).

set -e

cd misc/coqdep-string-literals

code=0
# List the files explicitly: the order of a glob depends on the locale's
# collation, and Lib.v sorts differently from the lowercase names on macOS.
$coqdep -worker @ROCQWORKER@ -R . 'Test' Lib.v dot_in_notation.v dot_in_string.v escaped_quote_in_string.v paren_in_string.v require_after_string.v > stdout 2> stderr || code=$?

diff -u stdout.ref stdout
diff -u stderr.ref stderr

exit $code
