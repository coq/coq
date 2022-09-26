#!/usr/bin/env bash

set -e

cd coqdep-require-filter-categories

coqdep -R . 'Bla' ./*.v > stdout 2> stderr

diff stdout.ref stdout
diff stderr.ref stderr
