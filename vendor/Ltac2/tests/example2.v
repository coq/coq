Require Import Ltac2.Ltac2.

Import Ltac2.Notations.

Set Default Goal Selector "all".

Goal exists n, n = 0.
Proof.
split with (x := 0).
reflexivity.
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

Goal forall (P : nat -> Prop), (forall n m, n = m -> P n) -> (0 = 1) -> P 0.
Proof.
intros P H e.
apply &H with (m := 1) in e.
exact e.
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
rewrite <- &He by assumption.
Control.refine (fun () => &He'').
Qed.

Goal forall n (r := if true then n else 0), r = n.
Proof.
intros n r.
hnf in r.
split.
Qed.

Goal 1 = 0 -> 0 = 0.
Proof.
intros H.
pattern 0 at 1.
let occ := 2 in pattern 1 at 1, 0 at $occ in H.
reflexivity.
Qed.

Goal 1 + 1 = 2.
Proof.
vm_compute.
reflexivity.
Qed.

Goal 1 + 1 = 2.
Proof.
native_compute.
reflexivity.
Qed.

Goal 1 + 1 = 2 - 0 -> True.
Proof.
intros H.
vm_compute plus in H.
reflexivity.
Qed.

Goal 1 = 0 -> True /\ True.
Proof.
intros H.
split; fold (1 + 0) (1 + 0) in H.
reflexivity.
Qed.

Goal 1 + 1 = 2.
Proof.
cbv [ Nat.add ].
reflexivity.
Qed.

Goal 1 + 1 = 2.
Proof.
let x := reference:(Nat.add) in
cbn beta iota delta [ $x ].
reflexivity.
Qed.

Goal 1 + 1 = 2.
Proof.
simpl beta.
reflexivity.
Qed.

Goal 1 + 1 = 2.
Proof.
lazy.
reflexivity.
Qed.

Goal let x := 1 + 1 - 1 in x = x.
Proof.
intros x.
unfold &x at 1.
let x := reference:(Nat.sub) in unfold Nat.add, $x in x.
reflexivity.
Qed.

Goal exists x y : nat, x = y.
Proof.
exists 0, 0; reflexivity.
Qed.

Goal exists x y : nat, x = y.
Proof.
eexists _, 0; reflexivity.
Qed.

Goal exists x y : nat, x = y.
Proof.
refine '(let x := 0 in _).
eexists; exists &x; reflexivity.
Qed.

Goal True.
Proof.
pose (X := True).
constructor.
Qed.

Goal True.
Proof.
pose True as X.
constructor.
Qed.

Goal True.
Proof.
let x := @foo in
set ($x := True) in * |-.
constructor.
Qed.

Goal 0 = 0.
Proof.
remember 0 as n eqn: foo at 1.
rewrite foo.
reflexivity.
Qed.

Goal True.
Proof.
assert (H := 0 + 0).
constructor.
Qed.

Goal True.
Proof.
assert (exists n, n = 0) as [n Hn].
+ exists 0; reflexivity.
+ exact I.
Qed.

Goal True -> True.
Proof.
assert (H : 0 + 0 = 0) by reflexivity.
intros x; exact x.
Qed.

Goal 1 + 1 = 2.
Proof.
change (?a + 1 = 2) with (2 = $a + 1).
reflexivity.
Qed.

Goal (forall n, n = 0 -> False) -> False.
Proof.
intros H.
specialize (H 0 eq_refl).
destruct H.
Qed.

Goal (forall n, n = 0 -> False) -> False.
Proof.
intros H.
specialize (H 0 eq_refl) as [].
Qed.
