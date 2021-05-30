Require Import ssreflect.

Section Apply.

Variable P : nat -> Prop.
Lemma test_apply A B : forall (f : A -> B) (a : A), B.

Proof.
move=> /[apply] b.
exact.
Qed.

End Apply.
