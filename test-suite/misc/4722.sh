#!/bin/sh
set -e

# create test files
mkdir -p misc/4722
ln -sf toto misc/4722/tata
touch misc/4722.v

# run test
$coqtop "-R" "misc/4722" "Foo" -top Top -load-vernac-source misc/4722.v

# clean up test files
rm misc/4722/tata
rmdir misc/4722
rm misc/4722.v
