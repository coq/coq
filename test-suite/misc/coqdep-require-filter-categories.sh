#!/usr/bin/env bash

set -e

cd misc/coqdep-require-filter-categories

$coqdep -worker @COQWORKER@ -R . 'Bla' ./*.v > stdout 2> stderr

diff stdout.ref stdout
diff stderr.ref stderr
