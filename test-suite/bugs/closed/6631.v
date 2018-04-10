Require Import Coq.derive.Derive.

Derive f SuchThat (f = 1 + 1) As feq.
Proof.
  transitivity 2; [refine (eq_refl 2)|].
  transitivity 2.
  2:abstract exact (eq_refl 2).
