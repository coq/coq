
Axiom admit : False.
Ltac admit := abstract destruct admit.

Axiom T : nat -> Type.
Axiom n : nat.

Lemma sorted_put (m:list (T n)) : false = true.
Proof.
  destruct m eqn:?Hmm.
  all:admit.
Qed.
