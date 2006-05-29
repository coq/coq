Set Implicit Arguments.

Notation "'fun' { x : A | P } => Q" :=
  (fun x:{x:A|P} => Q)
  (at level 200, x ident, right associativity).

Notation "( x & y )" := (@existS _ _ x y) : core_scope.

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


Notation "` t" := (proj1_sig t) (at level 100) : core_scope.
Notation "'forall' { x : A | P } , Q" :=
  (forall x:{x:A|P}, Q)
  (at level 200, x ident, right associativity).

Lemma subset_simpl : forall (A : Set) (P : A -> Prop) 
	(t : sig P), P (` t).
Proof.
intros.
induction t.
 simpl ; auto.
Qed.

