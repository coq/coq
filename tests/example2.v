Require Import Ltac2.Ltac2.

Import Ltac2.Notations.

Goal exists n, n = 0.
Proof.
split with (x := 0).
Std.reflexivity ().
Qed.

Goal exists n, n = 0.
Proof.
split with 0.
split.
Qed.

Goal exists n, n = 0.
Proof.
let myvar := Std.NamedHyp @x in split with (?myvar := 0).
split.
Qed.

Goal (forall n : nat, n = 0 -> False) -> True.
Proof.
intros H.
eelim &H.
split.
Qed.

Goal (forall n : nat, n = 0 -> False) -> True.
Proof.
intros H.
elim &H with 0.
split.
Qed.

Goal forall (P : nat -> Prop), (forall n m, n = m -> P n) -> P 0.
Proof.
intros P H.
Fail apply &H.
apply &H with (m := 0).
split.
Qed.

Goal forall (P : nat -> Prop), (forall n m, n = m -> P n) -> P 0.
Proof.
intros P H.
eapply &H.
split.
Qed.

Goal exists n, n = 0.
Proof.
Fail constructor 1.
constructor 1 with (x := 0).
split.
Qed.

Goal exists n, n = 0.
Proof.
econstructor 1.
split.
Qed.
