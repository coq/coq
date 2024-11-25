From Corelib Require Import Setoid ssreflect.

Lemma test A (R : relation A) `{Equivalence _ R} (x y z : A) :
  R x y -> R y z -> R x z.
Proof.
  intros Hxy Hyz.
  rewrite -Hxy in Hyz.
  exact Hyz.
Qed.



Axiom envs_lookup_delete : bool.
Axiom envs_lookup_delete_Some : envs_lookup_delete = true <-> False.

Goal envs_lookup_delete = true -> False.
Proof.
intros Hlookup.
rewrite envs_lookup_delete_Some in Hlookup *. (* <- used to revert Hlookup *)
exact Hlookup.
Qed.
