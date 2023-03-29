Inductive foo (n := 0) := Foo.

Goal foo -> True.
Proof.
intros H.
destruct H.
constructor.
Qed.

Goal foo -> True.
Proof.
intros H.
induction H.
constructor.
Qed.
