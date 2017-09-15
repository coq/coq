Require Import Program.

Axiom t : nat -> Set.

Goal forall (x y : nat) (e : x = y) (e' : x = y) (P : t y -> x = y -> Type)
       (a : t x),
    P (eq_rect _ _ a _ e) e'.
Proof.
  intros.
  pi_eq_proofs. clear e.
  destruct e'. simpl.
  change (P a eq_refl).
Abort.
