Require Import Corelib.derive.Derive.

Derive f in (f = 1 + 1) as feq.
Proof.
  transitivity 2; [refine (eq_refl 2)|].
  transitivity 2.
  2:abstract exact (eq_refl 2).
Abort.
