#!/bin/sh

set -ex

export COQBIN=$BIN
export PATH="$COQBIN:$PATH"

cd misc/comment-lexing/
rm -rf _test
mkdir _test
cp test.v _test

cd _test

rocq c -d comment-lexing -beautify test.v > test.out.real 2>&1

diff -u ../test.out test.out.real

diff -u ../test.v.beautified test.v.beautified
