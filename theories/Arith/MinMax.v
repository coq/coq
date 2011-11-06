(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Orders NatOrderedType GenericMinMax.

(** * Maximum and Minimum of two natural numbers *)

Fixpoint max n m : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m : nat :=
  match n, m with
    | O, _ => 0
    | S n', O => 0
    | S n', S m' => S (min n' m')
  end.

(** These functions implement indeed a maximum and a minimum *)

Lemma max_l : forall x y, y<=x -> max x y = x.
Proof.
 induction x; destruct y; simpl; auto with arith.
Qed.

Lemma max_r : forall x y, x<=y -> max x y = y.
Proof.
 induction x; destruct y; simpl; auto with arith.
Qed.

Lemma min_l : forall x y, x<=y -> min x y = x.
Proof.
 induction x; destruct y; simpl; auto with arith.
Qed.

Lemma min_r : forall x y, y<=x -> min x y = y.
Proof.
 induction x; destruct y; simpl; auto with arith.
Qed.


Module NatHasMinMax <: HasMinMax Nat_as_OT.
 Definition max := max.
 Definition min := min.
 Definition max_l := max_l.
 Definition max_r := max_r.
 Definition min_l := min_l.
 Definition min_r := min_r.
End NatHasMinMax.

(** We obtain hence all the generic properties of [max] and [min],
    see file [GenericMinMax] or use SearchAbout. *)

Module Export MMP := UsualMinMaxProperties Nat_as_OT NatHasMinMax.


(** * Properties specific to the [nat] domain *)

(** Simplifications *)

Lemma max_0_l : forall n, max 0 n = n.
Proof. reflexivity. Qed.

Lemma max_0_r : forall n, max n 0 = n.
Proof. destruct n; auto. Qed.

Lemma min_0_l : forall n, min 0 n = 0.
Proof. reflexivity. Qed.

Lemma min_0_r : forall n, min n 0 = 0.
Proof. destruct n; auto. Qed.

(** Compatibilities (consequences of monotonicity) *)

Lemma succ_max_distr : forall n m, S (max n m) = max (S n) (S m).
Proof. auto. Qed.

Lemma succ_min_distr : forall n m, S (min n m) = min (S n) (S m).
Proof. auto. Qed.

Lemma plus_max_distr_l : forall n m p, max (p + n) (p + m) = p + max n m.
Proof.
intros. apply max_monotone. repeat red; auto with arith.
Qed.

Lemma plus_max_distr_r : forall n m p, max (n + p) (m + p) = max n m + p.
Proof.
intros. apply max_monotone with (f:=fun x => x + p).
repeat red; auto with arith.
Qed.

Lemma plus_min_distr_l : forall n m p, min (p + n) (p + m) = p + min n m.
Proof.
intros. apply min_monotone. repeat red; auto with arith.
Qed.

Lemma plus_min_distr_r : forall n m p, min (n + p) (m + p) = min n m + p.
Proof.
intros. apply min_monotone with (f:=fun x => x + p).
repeat red; auto with arith.
Qed.

Hint Resolve
 max_l max_r le_max_l le_max_r
 min_l min_r le_min_l le_min_r : arith v62.
