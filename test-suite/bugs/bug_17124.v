Set Warnings "+bad-relevance".

Axiom P : SProp.
Axiom Q : P -> Type.
Axiom admit : False.

Lemma foo p : Q p.
Proof.
elim admit.
Qed.
