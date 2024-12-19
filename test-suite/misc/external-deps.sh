#!/bin/sh

set -e

# Set Extra Dependency syntax
output=misc/external-deps/file1.found.real
$coqdep -worker @ROCQWORKER@ -Q misc/external-deps/deps foo.bar misc/external-deps/file1.v > $output 2>&1
diff -u --strip-trailing-cr misc/external-deps/file1.found.deps $output

output=misc/external-deps/file1.ambiguous.real
$coqdep -worker @ROCQWORKER@ -Q misc/external-deps/deps foo.bar -Q misc/external-deps/more foo.bar misc/external-deps/file1.v > $output 2>&1
diff -u --strip-trailing-cr misc/external-deps/file1.ambiguous.deps $output

output=misc/external-deps/file1.notfound.real
$coqdep -worker @ROCQWORKER@ misc/external-deps/file1.v > $output 2>&1
diff -u --strip-trailing-cr misc/external-deps/file1.notfound.deps $output

# From bla Extra Dependency syntax
output=misc/external-deps/file2.found.real
$coqdep -worker @ROCQWORKER@ -Q misc/external-deps/deps foo.bar misc/external-deps/file2.v > $output 2>&1
diff -u --strip-trailing-cr misc/external-deps/file2.found.deps $output

output=misc/external-deps/file2.ambiguous.real
$coqdep -worker @ROCQWORKER@ -Q misc/external-deps/deps foo.bar -Q misc/external-deps/more foo.bar misc/external-deps/file2.v > $output 2>&1
diff -u --strip-trailing-cr misc/external-deps/file2.ambiguous.deps $output

output=misc/external-deps/file2.notfound.real
$coqdep -worker @ROCQWORKER@ misc/external-deps/file2.v > $output 2>&1
diff -u --strip-trailing-cr misc/external-deps/file2.notfound.deps $output
