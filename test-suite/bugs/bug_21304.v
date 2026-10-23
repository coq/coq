
Inductive equal T (x : T) : T -> Type := Equal : equal T x x.

Lemma foo : forall a b, equal nat a b -> a = b.
Proof.
intros a b H.
Fail rewrite <- H, H.
Abort.
