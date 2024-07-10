From Stdlib Require Import Reals Lra.

Open Scope R_scope.

Set Mangle Names.

Lemma div2mult05_0 : forall r, r / 2 = r * 0.5.
Proof.
  intros r.
  lra.
Qed.
