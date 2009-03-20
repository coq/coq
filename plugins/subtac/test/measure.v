Notation "( x & y )" := (@existS _ _ x y) : core_scope.
Unset Printing All.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.Program.Program.

Fixpoint size (a : nat) : nat :=
  match a with
  0 => 1
  | S n => S (size n)
  end.

Program Fixpoint test_measure (a : nat) {measure size a}  : nat :=
  match a with
  | S (S n) => S (test_measure n)
  | 0 | S 0 => a
  end.

Check test_measure.
Print test_measure.