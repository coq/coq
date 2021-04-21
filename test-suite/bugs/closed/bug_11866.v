Require Import Ltac2.Ltac2.

Ltac2 Notation "ex0" x(tactic(0)) := ().
Ltac2 Notation "ex1" x(tactic(1)) := ().
Ltac2 Notation "ex2" x(tactic(2)) := ().
Ltac2 Notation "ex3" x(tactic(3)) := ().
Ltac2 Notation "ex4" x(tactic(4)) := ().
Ltac2 Notation "ex5" x(tactic(5)) := ().
Ltac2 Notation "ex6" x(tactic(6)) := ().

Ltac2 Notation ":::0" x(tactic) "+0" y(tactic) : 0 := ().
Ltac2 Notation ":::1" x(tactic) "+1" y(tactic) : 1 := ().
Ltac2 Notation ":::2" x(tactic) "+2" y(tactic) : 2 := ().
Ltac2 Notation ":::3" x(tactic) "+3" y(tactic) : 3 := ().
Ltac2 Notation ":::4" x(tactic) "+4" y(tactic) : 4 := ().
Ltac2 Notation ":::5" x(tactic) "+5" y(tactic) : 5 := ().
Ltac2 Notation ":::6" x(tactic) "+6" y(tactic) : 6 := ().
Fail Ltac2 Notation ":::7" x(tactic) "+7" y(tactic) : 7 := ().
Goal True.
  ex0 :::0 0 +0 0.
  ex1 :::0 0 +0 0.
  (*ex2 :::0 0 +0 0.*) (* fails with an anomaly, cf COQBUG(https://github.com/coq/coq/issues/12807) *)
  (*ex3 :::0 0 +0 0.*)
  ex4 :::0 0 +0 0.
  ex5 :::0 0 +0 0.
  ex6 :::0 0 +0 0.

  ex0 :::1 0 +1 0.
  ex1 :::1 0 +1 0.
  (*ex2 :::1 0 +1 0.*)
  (*ex3 :::1 0 +1 0.*)
  ex4 :::1 0 +1 0.
  ex5 :::1 0 +1 0.
  ex6 :::1 0 +1 0.

  ex0 :::6 0 +6 0.
  ex1 :::6 0 +6 0.
  (*ex2 :::6 0 +6 0.*)
  (*ex3 :::6 0 +6 0.*)
  ex4 :::6 0 +6 0.
  ex5 :::6 0 +6 0.
  ex6 :::6 0 +6 0.
Abort.
