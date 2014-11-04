Lemma Foo : forall x y : nat, y = x -> y = x.
Proof.
intros x y.
rename x into y, y into x.
trivial.
Qed.

