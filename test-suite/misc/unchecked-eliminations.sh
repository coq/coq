#!/usr/bin/env bash

# There is intentionally no vernacular setter for the [check_eliminations]
# typing flag. This test builds a tiny plugin that toggles it via
# [Global.set_typing_flags] (the way rocq-lean-import does), declares a
# squashed Prop inductive with a large elimination while the flag is off, and
# checks that both [Print Assumptions] and [rocq check] report it.

set -ex

export COQBIN=$BIN
export PATH=$COQBIN:$PATH
export LC_ALL=C

cd misc/unchecked-eliminations/

rocq makefile -f _CoqProject -o Makefile

make clean

make src/elim_flag_plugin.cmxs

# Compile the .v, capturing the Print Assumptions / Print Typing Flags output.
rocq c -I src -Q theories UncheckedElim theories/unchecked.v 2>&1 | tee log

# checked_or (declared with the flag on) must NOT be reported.
# Anchor at line start so this does not match "unchecked_or".
grep -q "^checked_or relies on unchecked sort eliminations" log && {
  >&2 echo "checked_or should not rely on unchecked eliminations"
  exit 1
}

# unchecked_or and its constructors (declared with the flag off) must be
# reported as relying on unchecked sort eliminations.
grep -q "^unchecked_or relies on unchecked sort eliminations" log
grep -q "^unchecked_l relies on unchecked sort eliminations" log
grep -q "^unchecked_r relies on unchecked sort eliminations" log

# The theory summary line appears under Set Printing All Assumptions.
grep -q "Sort elimination constraints are not checked (logic is inconsistent)" log

# Print Typing Flags reports the flag.
grep -q "check_eliminations:" log

# rocq check must report the inductive in its context summary.
rocq check -Q theories UncheckedElim -o -silent -norec UncheckedElim.unchecked 2>&1 | tee chklog

grep -q "Constants/Inductives relying on unchecked sort eliminations" chklog
grep -q "UncheckedElim.unchecked.unchecked_or" chklog
