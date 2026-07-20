#!/usr/bin/env bash

set -e

cd misc/coqdep-require-safe

$coqdep -worker @ROCQWORKER@ -Q . Pfx Foo.v bare.v frombare.v fromsafe.v safe.v > stdout 2> stderr

diff -u stdout.ref stdout
diff -u stderr.ref stderr
