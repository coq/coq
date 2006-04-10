Set Implicit Arguments.

Definition ex_pi1 (A : Prop) (P : A -> Prop) (t : ex P) : A.
intros.
induction t.
exact x.
Defined.

Check proj1_sig.
Lemma subset_simpl : forall (A : Set) (P : A -> Prop)
  (t : sig P), P (proj1_sig t).
Proof.
intros.
induction t.
 simpl ; auto.
Qed.

Lemma ex_pi2  : forall (A : Prop) (P : A -> Prop) (t : ex P),
 P (ex_pi1 t).
intros A P.
dependent inversion t.
simpl.
exact p.
Defined.

Notation "'forall' { x : A | P } , Q" :=
  (forall x:{x:A|P}, Q)
  (at level 200, x ident, right associativity).

Notation "'fun' { x : A | P } => Q" :=
  (fun x:{x:A|P} => Q)
  (at level 200, x ident, right associativity).

Notation "( x & y )" := (@existS _ _ x y) : core_scope.
