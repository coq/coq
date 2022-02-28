Parameter A : Type.

Parameter f : A -> A.
Parameter P : A -> Prop.
Parameter H : forall a, P (f a) -> Prop.

Lemma Foo : forall a (p : P (f a)), H a p.
Proof.
intros a p.
Fail remember (f a) as b.
Abort.
