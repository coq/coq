(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type [nat] of Peano natural numbers (built from [O] and [S])
    is defined in [Datatypes.v] *)

(** This module defines the following operations on natural numbers :
    - predecessor [pred]
    - addition [plus]
    - multiplication [mult]
    - less or equal order [le]
    - less [lt]
    - greater or equal [ge]
    - greater [gt]

   It states various lemmas and theorems about natural numbers,
   including Peano's axioms of arithmetic (in Rocq, these are provable).
   Case analysis on [nat] and induction on [nat * nat] are provided too
 *)

Require Import Notations.
Require Import Ltac.
Require Import Datatypes.
Require Import Logic.
Require Corelib.Init.Nat.

Open Scope nat_scope.
Local Notation "0" := O.

Definition eq_S := f_equal S.
Definition f_equal_nat := f_equal (A:=nat).

#[global]
Hint Resolve f_equal_nat: core.

(** The predecessor function *)

Notation pred := Nat.pred (only parsing).

Definition f_equal_pred := f_equal pred.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  simpl; reflexivity.
Qed.

(** Injectivity of successor *)

Definition eq_add_S n m (H: S n = S m): n = m := f_equal pred H.
#[global]
Hint Immediate eq_add_S: core.

Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Proof.
  red; auto.
Qed.
#[global]
Hint Resolve not_eq_S: core.

Definition IsSucc (n:nat) : Prop :=
  match n with
  | O => False
  | S p => True
  end.

(** Zero is not the successor of a number *)

Theorem O_S : forall n:nat, 0 <> S n.
Proof.
  discriminate.
Qed.
#[global]
Hint Resolve O_S: core.

Theorem n_Sn : forall n:nat, n <> S n.
Proof.
  intro n; induction n; auto.
Qed.
#[global]
Hint Resolve n_Sn: core.

(** Addition *)

Notation plus := Nat.add (only parsing).
Infix "+" := Nat.add : nat_scope.

Definition f_equal2_plus := f_equal2 plus.
Definition f_equal2_nat := f_equal2 (A1:=nat) (A2:=nat). 
#[global]
Hint Resolve f_equal2_nat: core.

Lemma plus_n_O : forall n:nat, n = n + 0.
Proof.
  intro n; induction n; simpl; auto.
Qed.

#[global]
Remove Hints eq_refl : core.
#[global]
Hint Resolve plus_n_O eq_refl: core.  (* We want eq_refl to have higher priority than plus_n_O *)

Lemma plus_O_n : forall n:nat, 0 + n = n.
Proof.
  reflexivity.
Qed.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl; auto.
Qed.
#[global]
Hint Resolve plus_n_Sm: core.

Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof.
  reflexivity.
Qed.

(** Standard associated names *)

Notation plus_0_r_reverse := plus_n_O (only parsing).
Notation plus_succ_r_reverse := plus_n_Sm (only parsing).

(** Multiplication *)

Notation mult := Nat.mul (only parsing).
Infix "*" := Nat.mul : nat_scope.

Definition f_equal2_mult := f_equal2 mult.
#[global]
Hint Resolve f_equal2_mult: core.

Lemma mult_n_O : forall n:nat, 0 = n * 0.
Proof.
  intro n; induction n; simpl; auto.
Qed.
#[global]
Hint Resolve mult_n_O: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros n m; induction n as [| p H]; simpl; auto.
  destruct H; rewrite <- plus_n_Sm; apply eq_S.
  pattern m at 1 3; elim m; simpl; auto.
Qed.
#[global]
Hint Resolve mult_n_Sm: core.

(** Standard associated names *)

Notation mult_0_r_reverse := mult_n_O (only parsing).
Notation mult_succ_r_reverse := mult_n_Sm (only parsing).

(** Truncated subtraction: [m-n] is [0] if [n>=m] *)

Notation minus := Nat.sub (only parsing).
Infix "-" := Nat.sub : nat_scope.

(** Definition of the usual orders, the basic properties of [le] and [lt]
    can be found in files Le and Lt *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.

Register le_n as num.nat.le_n.

#[global]
Hint Constructors le: core.
(*i equivalent to : "Hints Resolve le_n le_S : core." i*)

Definition lt (n m:nat) := S n <= m.
#[global]
Hint Unfold lt: core.

Infix "<" := lt : nat_scope.

Definition ge (n m:nat) := m <= n.
#[global]
Hint Unfold ge: core.

Infix ">=" := ge : nat_scope.

Definition gt (n m:nat) := m < n.
#[global]
Hint Unfold gt: core.

Infix ">" := gt : nat_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.

Register le as num.nat.le.
Register lt as num.nat.lt.
Register ge as num.nat.ge.
Register gt as num.nat.gt.

Theorem le_pred : forall n m, n <= m -> pred n <= pred m.
Proof.
induction 1 as [|m _]; auto. destruct m; simpl; auto.
Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
intros n m. exact (le_pred (S n) (S m)).
Qed.

Theorem le_0_n : forall n, 0 <= n.
Proof.
 intro n; induction n; constructor; trivial.
Qed.

Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Proof.
 induction 1; constructor; trivial.
Qed.

(** Case analysis *)

Theorem nat_case :
 forall (n:nat) (P:nat -> Prop), P 0 -> (forall m:nat, P (S m)) -> P n.
Proof.
  intros n P IH0 IHS; case n; auto.
Qed.

(** Principle of double induction *)

Theorem nat_double_ind :
 forall R:nat -> nat -> Prop,
   (forall n:nat, R 0 n) ->
   (forall n:nat, R (S n) 0) ->
   (forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.
Proof.
  intros R ? ? ? n.
  induction n; auto.
  intro m; destruct m; auto.
Qed.

(** Maximum and minimum : definitions and specifications *)

Notation max := Nat.max (only parsing).
Notation min := Nat.min (only parsing).

Lemma max_l n m : m <= n -> Nat.max n m = n.
Proof.
 revert m; induction n as [|n IHn]; intro m; destruct m; simpl; trivial.
 - inversion 1.
 - intros. apply f_equal, IHn, le_S_n; trivial.
Qed.

Lemma max_r n m : n <= m -> Nat.max n m = m.
Proof.
 revert m; induction n as [|n IHn]; intro m; destruct m; simpl; trivial.
 - inversion 1.
 - intros. apply f_equal, IHn, le_S_n; trivial.
Qed.

Lemma min_l n m : n <= m -> Nat.min n m = n.
Proof.
 revert m; induction n as [|n IHn]; intro m; destruct m; simpl; trivial.
 - inversion 1.
 - intros. apply f_equal, IHn, le_S_n; trivial.
Qed.

Lemma min_r n m : m <= n -> Nat.min n m = m.
Proof.
 revert m; induction n as [|n IHn]; intro m; destruct m; simpl; trivial.
 - inversion 1.
 - intros. apply f_equal, IHn, le_S_n; trivial.
Qed.


Lemma nat_rect_succ_r {A} (f: A -> A) (x:A) n :
  nat_rect (fun _ => A) x (fun _ => f) (S n) = nat_rect (fun _ => A) (f x) (fun _ => f) n.
Proof.
  induction n as [|n IHn]; intros; simpl; rewrite <- ?IHn; trivial.
Qed.

Theorem nat_rect_plus :
  forall (n m:nat) {A} (f:A -> A) (x:A),
    nat_rect (fun _ => A) x (fun _ => f) (n + m) =
      nat_rect (fun _ => A) (nat_rect (fun _ => A) x (fun _ => f) m) (fun _ => f) n.
Proof.
  intro n; induction n as [|n IHn]; intros; simpl; rewrite ?IHn; trivial.
Qed.
