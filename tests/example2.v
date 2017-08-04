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
let myvar := Std.NamedHyp @x in split with ($myvar := 0).
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

Goal forall n, 0 + n = n.
Proof.
intros n.
induction &n as [|n] using nat_rect; split.
Qed.

Goal forall n, 0 + n = n.
Proof.
intros n.
let n := @X in
let q := Std.NamedHyp @P in
induction &n as [|$n] using nat_rect with ($q := fun m => 0 + m = m); split.
Qed.

Goal forall n, 0 + n = n.
Proof.
intros n.
destruct &n as [|n] using nat_rect; split.
Qed.

Goal forall n, 0 + n = n.
Proof.
intros n.
let n := @X in
let q := Std.NamedHyp @P in
destruct &n as [|$n] using nat_rect with ($q := fun m => 0 + m = m); split.
Qed.

Goal forall b1 b2, andb b1 b2 = andb b2 b1.
Proof.
intros b1 b2.
destruct &b1 as [|], &b2 as [|]; split.
Qed.

Goal forall n m, n = 0 -> n + m = m.
Proof.
intros n m Hn.
rewrite &Hn; split.
Qed.

Goal forall n m p, n = m -> p = m -> 0 = n -> p = 0.
Proof.
intros n m p He He' Hn.
rewrite &He, <- &He' in Hn.
rewrite &Hn.
split.
Qed.

Goal forall n m, (m = n -> n = m) -> m = n -> n = 0 -> m = 0.
Proof.
intros n m He He' He''.
rewrite <- &He by Std.assumption ().
Control.refine (fun () => &He'').
Qed.
