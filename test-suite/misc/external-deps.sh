#!/bin/sh

set -e

tmpoutput=$(mktemp /tmp/coqcheck.XXXXXX)

# Set Extra Dependency syntax
coqdep -Q external-deps/deps foo.bar external-deps/file1.v > $tmpoutput 2>&1
diff -u --strip-trailing-cr external-deps/file1.found.deps $tmpoutput

coqdep -Q external-deps/deps foo.bar -Q external-deps/more foo.bar external-deps/file1.v > $tmpoutput 2>&1
diff -u --strip-trailing-cr external-deps/file1.ambiguous.deps $tmpoutput

coqdep external-deps/file1.v > $tmpoutput 2>&1
diff -u --strip-trailing-cr external-deps/file1.notfound.deps $tmpoutput

# From bla Extra Dependency syntax
coqdep -Q external-deps/deps foo.bar external-deps/file2.v > $tmpoutput 2>&1
diff -u --strip-trailing-cr external-deps/file2.found.deps $tmpoutput

coqdep -Q external-deps/deps foo.bar -Q external-deps/more foo.bar external-deps/file2.v > $tmpoutput 2>&1
diff -u --strip-trailing-cr external-deps/file2.ambiguous.deps $tmpoutput

coqdep external-deps/file2.v > $tmpoutput 2>&1
diff -u --strip-trailing-cr external-deps/file2.notfound.deps $tmpoutput

rm -f $tmpoutput
