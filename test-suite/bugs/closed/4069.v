
Lemma test1 : 
forall (v : nat) (f g : nat -> nat),
f v = g v.
intros. f_equal.
(* 
Goal in v8.5: f v = g v
Goal in v8.4: v = v -> f v = g v
Expected: f = g
*)
Admitted.

Lemma test2 : 
forall (v u : nat) (f g : nat -> nat),
f v = g u.
intros. f_equal.
(* 
In both v8.4 And v8.5
Goal 1: v = u -> f v = g u
Goal 2: v = u

Expected Goal 1: f = g
Expected Goal 2: v = u
*)
Admitted.

Lemma test3 : 
forall (v : nat) (u : list nat) (f : nat -> nat) (g : list nat -> nat),
f v = g u.
intros. f_equal.
(* 
In both v8.4 And v8.5, the goal is unchanged.
*)
Admitted.

Require Import List.
Lemma foo n (l k : list nat) : k ++ skipn n l = skipn n l.
Proof. f_equal.
(*
  8.4: leaves the goal unchanged, i.e. k ++ skipn n l = skipn n l
  8.5: 2 goals, skipn n l = l -> k ++ skipn n l = skipn n l
    and skipn n l = l
*)
Abort.

Require Import List.
Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with 0 => nil | S n => x :: replicate n x end.
Lemma bar {A} n m (x : A) : 
  skipn n (replicate m x) = replicate (m - n) x ->
  skipn n (replicate m x) = replicate (m - n) x.
Proof. intros. f_equal.
(* 8.5: one goal, n = m - n *)
Abort.

Variable F : nat -> Set.
Variable X : forall n, F (n + 1).

Definition sequator{X Y: Set}{eq:X=Y}(x:X) : Y := eq_rec _ _ x _ eq.
Definition tequator{X Y}{eq:X=Y}(x:X) : Y := eq_rect _ _ x _ eq.
Polymorphic Definition pequator{X Y}{eq:X=Y}(x:X) : Y := eq_rect _ _ x _ eq.

Goal {n:nat & F (S n)}.
eexists.
unshelve eapply (sequator (X _)).
f_equal. (*behaves*)
Undo 2.
unshelve eapply (pequator (X _)).
f_equal. (*behaves*)
Undo 2.
unshelve eapply (tequator (X _)).
f_equal. (*behaves now *)
Focus 2. exact 0.
simpl.
reflexivity.
Defined.

(* Part 2: modulo casts introduced by refine due to reductions in goals *)

Goal {n:nat & F (S n)}.
eexists.
(*misbehaves, although same goal as above*)
Set Printing All.
unshelve refine (sequator (X _)); revgoals.
2:exact 0. reflexivity.
Undo 3. 
unshelve refine (pequator (X _)); revgoals.
f_equal.
Undo 2.
unshelve refine (tequator (X _)); revgoals.
f_equal.
Admitted.

Goal @eq Set nat nat.
congruence.
Qed.

Goal @eq Type nat nat.
congruence. 
Qed.

Variable T : Type.

Goal @eq Type T T.
congruence.
Qed.
