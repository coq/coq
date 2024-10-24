From Stdlib Require Import Program Arith.

Program Fixpoint check_n  (n : nat) (P : { i | i < n } -> bool) (p : nat)
  (H : forall (i : { i | i < n }), i < p -> P i = true)
  {measure (n - p)} :
  Exc (forall (p : { i | i < n}), P p = true) :=
  match le_lt_dec n p with
  | left _ => value _
  | right cmp =>
      if dec (P p) then
        check_n n P (S p) _
      else
        error
  end.

From Stdlib Require Import Lia.

Solve Obligations with program_simpl ; auto with *; lia.

Next Obligation.
  apply H. simpl. lia.
Defined.

Next Obligation.
  case (le_lt_dec p i) ; intros. assert(i = p) by lia. subst.
  revert e. clear_subset_proofs. auto.
  apply H. simpl. assumption. Defined.
