#!/bin/sh

set -ex

export COQBIN=$BIN
export PATH="$COQBIN:$PATH"

diff() {
  command diff -a -u --strip-trailing-cr "$1" "$2"
}

cd misc/comment-lexing/
rm -rf _test
mkdir _test
cp test.v _test

cd _test

rocq c -d comment-lexing -beautify test.v > test.out.real 2>&1

diff ../test.out test.out.real

diff ../test.v.beautified test.v.beautified
