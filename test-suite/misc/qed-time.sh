#!/usr/bin/env bash

set -ex

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/qed-time/

# This test checks that the Qed time includes the time of the replayed command

# The version of this test in output-modulo-time checks that each
# command gets 1 time line, but because output-modulo-time normalizes
# times to 0 it can't check that the replayed command is not ignored

rocq c -time file.v > out

last=$(tail -n 1 out)

last=${last#"Chars 98 - 102 [Qed.] "}
last=${last%" secs"*}

# sanity check: regex produces a float
[[ $last =~ [0-9]+"."[0-9]* ]]

test() {
    printf 'if %s <= 0.9:\n\texit (1)\n' "$1" | python3
}

# sanity checks: python works on the code we produce
if test 0.9; then exit 1; fi
test 1.
test 1.1

test "$last"
