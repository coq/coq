Create HintDb foo discriminated.

Definition myid (A : Prop) := A.

Section Test1.

#[local] Hint Constructors True : foo.

Lemma test1 : myid True.
Proof.
Fail typeclasses eauto with foo.
Abort.

End Test1.

Section Test2.

Definition hide (A : Prop) := A.

#[local] Hint Extern 1 => match goal with [ |- hide True ] => constructor end : foo.
#[local] Hint Unfold myid : foo.

Lemma test2 : hide (myid True).
Proof.
Fail typeclasses eauto with foo.
Abort.

End Test2.

Section Test3.

#[local] Hint Constructors True : foo.
#[local] Hint Unfold myid : foo.

Lemma test3 : myid True.
Proof.
typeclasses eauto with foo.
Qed.

End Test3.
