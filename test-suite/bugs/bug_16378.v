Universes u v.
Constraint u < v. (* or v < u *)
Axiom X : Type@{u} = Type@{v}.

Lemma foo : forall (P : Type@{u}), P -> P.
Proof.
  destruct X.
  intros P p; exact p.
Qed.
