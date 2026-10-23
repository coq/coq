#!/usr/bin/env bash

# There is intentionally no vernacular setter for the [check_eliminations]
# typing flag. This test builds a tiny plugin that toggles it via
# [Global.set_typing_flags] (the way rocq-lean-import does), declares a
# squashed Prop inductive with a large elimination while the flag is off, and
# compares the output of [Print Assumptions], [Print Typing Flags] and
# [rocq check] against reference files.

set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH
export LC_ALL=C

cd misc/unchecked-eliminations/

rocq makefile -f _CoqProject -o Makefile

make clean

make src/elim_flag_plugin.cmxs

rocq c -q -I src -Q theories UncheckedElim theories/unchecked.v > unchecked.out.real 2>&1
diff -u --strip-trailing-cr unchecked.out unchecked.out.real

rocq check -Q theories UncheckedElim -o -silent -norec UncheckedElim.unchecked > unchecked.chk.real 2>&1
diff -u --strip-trailing-cr unchecked.chk unchecked.chk.real
