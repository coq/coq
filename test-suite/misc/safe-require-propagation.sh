#!/usr/bin/env bash
# A library compiled with [Require (safe) M] keeps M (and M's dependencies)
# safe for its downstream users: requiring such a library fully loads it but
# only safe-loads its safe dependencies.

set -ex

export PATH=$BIN:$PATH

cd misc/safe-require-propagation
rm -rf _test
mkdir _test
find . -maxdepth 1 -not -name . -not -name _test -exec cp -r '{}' -t _test ';'
cd _test

# A safe-requires CMorphisms (which depends on CRelationClasses).
rocq c -R . Top A.v

# Requiring A fully must keep CRelationClasses safe (no implicit arguments,
# and a plain require of it is still rejected).
rocq c -test-mode -R . Top B.v > B.real 2>&1
diff -u --strip-trailing-cr B.out B.real

# fully requiring CRelationClasses first, then A, works and keeps
# CRelationClasses fully loaded.
rocq c -test-mode -R . Top C.v > C.real 2>&1
diff -u --strip-trailing-cr C.out C.real

# "Require A C" (in one command) full requires CRelationClasses because C does,
# even though the dep graph DFS sees the safe edge from A first
rocq c -test-mode -R . Top D.v > D.real 2>&1
diff -u --strip-trailing-cr D.out D.real

# separately requiring A then C fails because A safe requires CRelationClasses,
# then C full requires it
rocq c -test-mode -R . Top E.v > E.real 2>&1
diff -u --strip-trailing-cr E.out E.real
