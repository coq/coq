From Stdlib Require Import Uint63.
Open Scope uint63_scope.

Lemma foo :
  let n := opp 0 in add n 0 = n.
Proof.
cbv.
apply eq_refl.
Qed.
