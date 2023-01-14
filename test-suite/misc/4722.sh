#!/bin/sh
set -e

# create test files
mkdir -p 4722
ln -sf toto 4722/tata
touch bug_4722.v

# run test
coqc "-R" "4722" "Foo" -top Top bug_4722.v

# clean up test files
rm 4722/tata
rmdir 4722
rm bug_4722.v
