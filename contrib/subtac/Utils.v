Set Implicit Arguments.
Lemma subset_simpl : forall (A : Set) (P : A -> Prop)
  (t : sig P), P (proj1_sig t).
Proof.
intros.
induction t.
 simpl ; auto.
Qed.

Definition ex_pi1 (A : Prop) (P : A -> Prop) (t : ex P) : A.
intros.
induction t.
exact x.
Defined.

Lemma ex_pi2  : forall (A : Prop) (P : A -> Prop) (t : ex P),
 P (ex_pi1 t).
intros A P.
dependent inversion t.
simpl.
exact p.
Defined.
