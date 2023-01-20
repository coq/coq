Set Warnings "+bad-relevance".

Axiom T : SProp.
Axiom ind : forall (Hp : T) (P : T -> Type), P Hp.

Definition foo (p : T) : True.
Proof.
pattern p.
apply ind.
Qed. (* Bad relevance for binder t. *)
