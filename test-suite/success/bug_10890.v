Require Import Derive.

Derive foo in (foo = foo :> nat) as bar.
Proof.
  Unshelve.
  2:abstract exact 0.
   exact eq_refl.
Defined. (* or Qed: anomaly kernel doesn't support existential variables *)
