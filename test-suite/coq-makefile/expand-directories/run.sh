#!/usr/bin/env bash

. ../template/path-init.sh

rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'

cd _test || exit 1

# includes 6 file extensions, ignores others such as .c, .vo
# recursive expansion
# explicit non-existent file included
actual=`rocq makefile -sources-of -o CoqMakefile . nonexistent.v`
expected="a/b/g.v a/g.mlg a/g.mllib a/g.mlpack g.ml g.mli nonexistent.v"
if [ "$actual" != "$expected" ]; then
  echo actual: $actual
  echo expected: $expected
  exit 1
fi

# expands specific directory, not ., gets the right subset
actual=`rocq makefile -sources-of -o CoqMakefile a`
expected="a/b/g.v a/g.mlg a/g.mllib a/g.mlpack"
if [ "$actual" != "$expected" ]; then
  echo actual: $actual
  echo expected: $expected
  exit 1
fi

# command line args are in Makefile.conf
rocq makefile -o CoqMakefile . x
actual=`grep "COQMF_CMDLINE_VFILES := . x" CoqMakefile.conf`
if test $? -ne 0; then
  echo bad COQMF_CMDLINE_VFILES:
  grep "COQMF_CMDLINE_VFILES" CoqMakefile.conf
  exit 1
fi
