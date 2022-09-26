#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'

cd _test || exit 1

# check cmd line arg is included in coqdep
# preserves order of args (cmd line args last)
actual=$(coq_makefile -sources-of -f _CoqProject -o CoqMakefile b.v)
expected="x/a.v b.v"
if [ "$actual" != "$expected" ]; then
  echo actual: $actual
  echo expected: $expected
  exit 1
fi

# correct compile steps reflecting dependency on cmd line arg
coq_makefile -f _CoqProject -o CoqMakefile b.v
make -f CoqMakefile > makeout
cat >expected <<EOT
COQDEP VFILES
COQC b.v
COQC x/a.v
EOT

grep -v "make" makeout >actual
if [ "$(diff actual expected)" != "" ]; then
  echo expected:
  cat expected
  echo actual:
  cat actual
fi

# new file is included without running coq_makefile
cat >x/c.v <<EOT
EOT
make -f CoqMakefile clean
make -f CoqMakefile > makeout
cat >expected <<EOT
COQDEP VFILES
COQC b.v
COQC x/a.v
COQC x/c.v
EOT

grep -v "make" makeout >actual
if [ "$(diff actual expected)" != "" ]; then
  echo expected:
  cat expected
  echo actual:
  cat actual
fi
