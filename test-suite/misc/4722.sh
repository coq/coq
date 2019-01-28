#!/bin/sh
set -e

# create test files
mkdir -p misc/4722
ln -sf toto misc/4722/tata
touch misc/bug_4722.v

# run test
$coqc "-R" "misc/4722" "Foo" -top Top misc/bug_4722.v

# clean up test files
rm misc/4722/tata
rmdir misc/4722
rm misc/bug_4722.v
