Notation "( x & y )" := (@existS _ _ x y) : core_scope.
Unset Printing All.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.subtac.Utils.

Fixpoint size (a : nat) : nat :=
  match a with
  0 => 1
  | S n => S (size n)
  end.

Program Fixpoint test_measure (a : nat) {measure a size}  : nat :=
  match a with
  | S (S n) => S (test_measure n)
  | x => x
  end.
subst.
unfold n0.
auto with arith.
Qed.

Check test_measure.
Print test_measure.