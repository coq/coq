Require Import PrimInt63.
Open Scope uint63_scope.

Definition opp i := sub 0 i.

Lemma foo :
  let n := opp 0 in add n 0 = n.
Proof.
cbv.
apply eq_refl.
Qed.
