#!/bin/sh
set -e

# run test
$coqc "-R" "misc/10212" "Test" misc/10212/A.v
$coqc "-R" "misc/10212" "Test" misc/10212/B.v
