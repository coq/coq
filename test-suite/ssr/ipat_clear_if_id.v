Require Import ssreflect.

Axiom v1 : nat -> bool.

Section Foo.

Variable v2 : nat -> bool.

Lemma test (v3 : nat -> bool) (v4 : bool -> bool) (v5 : bool -> bool) : nat -> nat -> nat -> nat -> True.
Proof.
move=> {}/v1 b1 {}/v2 b2 {}/v3 b3 {}/v2/v4/v5 b4.
Check b1 : bool.
Check b2 : bool.
Check b3 : bool.
Check b4 : bool.
Fail Check v3.
Fail Check v4.
Fail Check v5.
Check v2 : nat -> bool.
by [].
Qed.

End Foo.
