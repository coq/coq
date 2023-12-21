Require Import PrimFloat.
Open Scope float_scope.

Lemma foo :
  let n := opp 0 in sub n 0 = n.
Proof.
cbv.
apply eq_refl.
Qed.
