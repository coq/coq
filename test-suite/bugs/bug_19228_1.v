Axiom decidable : Prop -> Set.

Class Dec_Eq (A : Type) := { dec_eq : forall (x y : A), decidable (x = y) }.

Lemma Dec_Eq_implies_DecEq {A} {H : Dec_Eq A} (x y : A) : decidable (x = y).
Proof.
apply H.
Qed.
