Require Export BigN.
Require Import ZMake.


Module BigZ := Make BigN.


Definition bigZ := BigZ.t.

Delimit Scope bigZ_scope with bigZ.
Bind Scope bigZ_scope with bigZ.
Bind Scope bigZ_scope with BigZ.t.
Bind Scope bigZ_scope with BigZ.t_.

Notation " i + j " := (BigZ.add i j) : bigZ_scope.
Notation " i - j " := (BigZ.sub i j) : bigZ_scope.
Notation " i * j " := (BigZ.mul i j) : bigZ_scope.
Notation " i / j " := (BigZ.div i j) : bigZ_scope.
Notation " i ?= j " := (BigZ.compare i j) : bigZ_scope.
