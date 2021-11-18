Require Import ssreflect.

Section Foo.
Variable x : nat.

Lemma toto : True /\ True.
Proof.
  have y : True by [].
  by split.
Qed.

Print toto.

End Foo.

Print toto.
