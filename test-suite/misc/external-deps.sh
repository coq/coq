#!/bin/sh

set -e

# Set Extra Dependency syntax
output=misc/external-deps/file1.found.real
if ! $coqdep -worker @ROCQWORKER@ -Q misc/external-deps/deps foo.bar misc/external-deps/file1.v > $output 2>&1; then
  >&2 echo file1.found failed
  exit 1
fi
diff -u --strip-trailing-cr misc/external-deps/file1.found.deps $output

output=misc/external-deps/file1.ambiguous.real
if ! $coqdep -worker @ROCQWORKER@ -Q misc/external-deps/deps foo.bar -Q misc/external-deps/more foo.bar misc/external-deps/file1.v > $output 2>&1; then
  >&2 echo file1.ambiguous failed
  exit 1
fi
diff -u --strip-trailing-cr misc/external-deps/file1.ambiguous.deps $output

output=misc/external-deps/file1.notfound.error.real
if $coqdep -worker @ROCQWORKER@ misc/external-deps/file1.v > $output 2>&1; then
  >&2 echo file1.notfound.error did not fail
  exit 1
fi
diff -u --strip-trailing-cr misc/external-deps/file1.notfound.error.deps $output

output=misc/external-deps/file1.notfound.warn.real
if ! $coqdep -worker @ROCQWORKER@ misc/external-deps/file1.v -w module-not-found > $output 2>&1; then
  >&2 echo file1.warn failed
  exit 1
fi
diff -u --strip-trailing-cr misc/external-deps/file1.notfound.warn.deps $output

# From bla Extra Dependency syntax
output=misc/external-deps/file2.found.real
if ! $coqdep -worker @ROCQWORKER@ -Q misc/external-deps/deps foo.bar misc/external-deps/file2.v > $output 2>&1; then
  >&2 echo file1.found failed
  exit 1
fi
diff -u --strip-trailing-cr misc/external-deps/file2.found.deps $output

output=misc/external-deps/file2.ambiguous.real
if ! $coqdep -worker @ROCQWORKER@ -Q misc/external-deps/deps foo.bar -Q misc/external-deps/more foo.bar misc/external-deps/file2.v > $output 2>&1; then
  >&2 echo file1.ambiguous failed
  exit 1
fi
diff -u --strip-trailing-cr misc/external-deps/file2.ambiguous.deps $output

output=misc/external-deps/file2.notfound.error.real
if $coqdep -worker @ROCQWORKER@ misc/external-deps/file2.v > $output 2>&1; then
  >&2 echo file2.notfound.error did not fail
  exit 1
fi
diff -u --strip-trailing-cr misc/external-deps/file2.notfound.error.deps $output

output=misc/external-deps/file2.notfound.warn.real
if ! $coqdep -worker @ROCQWORKER@ misc/external-deps/file2.v -w module-not-found > $output 2>&1; then
  >&2 echo file2.notfound.warn failed
  exit 1
fi
diff -u --strip-trailing-cr misc/external-deps/file2.notfound.warn.deps $output
