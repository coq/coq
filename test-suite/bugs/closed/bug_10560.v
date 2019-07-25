From Coq Require Import Int63.
Open Scope int63_scope.

Lemma foo :
  let n := opp 0 in add n 0 = n.
Proof.
cbv.
apply eq_refl.
Qed.
