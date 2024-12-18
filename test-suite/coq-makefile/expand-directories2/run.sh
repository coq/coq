#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'

cd _test || exit 1

# check cmd line arg is included in coqdep
# preserves order of args (cmd line args last)
actual=$(rocq makefile -sources-of -f _CoqProject -o CoqMakefile b.v)
expected="x/a.v b.v"
if [ "$actual" != "$expected" ]; then
  echo actual: $actual
  echo expected: $expected
  exit 1
fi

# correct compile steps reflecting dependency on cmd line arg
rocq makefile -f _CoqProject -o CoqMakefile b.v
make -f CoqMakefile > makeout
cat >expected <<EOT
ROCQ DEP VFILES
ROCQ compile b.v
ROCQ compile x/a.v
EOT

grep -v "make" makeout >actual
diff -u actual expected

# new file is included without running rocq makefile
cat >x/c.v <<EOT
Require Import T.x.a.
EOT
make -f CoqMakefile clean
make -f CoqMakefile > makeout
cat >expected <<EOT
ROCQ DEP VFILES
ROCQ compile b.v
ROCQ compile x/a.v
ROCQ compile x/c.v
EOT

grep -v "make" makeout >actual
diff -u actual expected
