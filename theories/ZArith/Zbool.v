(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt.
Require Import Zeven.
Require Import Zorder.
Require Import Zcompare.
Require Import ZArith_dec.
Require Import Sumbool.

Unset Boxed Definitions.
Open Local Scope Z_scope.

(** * Boolean operations from decidability of order *)
(** The decidability of equality and order relations over
    type [Z] gives some boolean functions with the adequate specification. *)

Definition Z_lt_ge_bool (x y:Z) := bool_of_sumbool (Z_lt_ge_dec x y).
Definition Z_ge_lt_bool (x y:Z) := bool_of_sumbool (Z_ge_lt_dec x y).

Definition Z_le_gt_bool (x y:Z) := bool_of_sumbool (Z_le_gt_dec x y).
Definition Z_gt_le_bool (x y:Z) := bool_of_sumbool (Z_gt_le_dec x y).

Definition Z_eq_bool (x y:Z) := bool_of_sumbool (Z_eq_dec x y).
Definition Z_noteq_bool (x y:Z) := bool_of_sumbool (Z_noteq_dec x y).

Definition Zeven_odd_bool (x:Z) := bool_of_sumbool (Zeven_odd_dec x).

(**********************************************************************)
(** * Boolean comparisons of binary integers *)

Definition Zle_bool (x y:Z) :=
  match x ?= y with
    | Gt => false
    | _ => true
  end.

Definition Zge_bool (x y:Z) :=
  match x ?= y with
    | Lt => false
    | _ => true
  end.

Definition Zlt_bool (x y:Z) :=
  match x ?= y with
    | Lt => true
    | _ => false
  end.

Definition Zgt_bool (x y:Z) :=
  match x ?= y with
    | Gt => true
    | _ => false
  end.

Definition Zeq_bool (x y:Z) :=
  match x ?= y with
    | Eq => true
    | _ => false
  end.

Definition Zneq_bool (x y:Z) :=
  match x ?= y with
    | Eq => false
    | _ => true
  end.

(** Properties in term of [if ... then ... else ...] *)

Lemma Zle_cases :
  forall n m:Z, if Zle_bool n m then (n <= m) else (n > m).
Proof.
  intros x y; unfold Zle_bool, Zle, Zgt in |- *.
  case (x ?= y); auto; discriminate.
Qed.

Lemma Zlt_cases :
  forall n m:Z, if Zlt_bool n m then (n < m) else (n >= m).
Proof.
  intros x y; unfold Zlt_bool, Zlt, Zge in |- *.
  case (x ?= y); auto; discriminate.
Qed.

Lemma Zge_cases :
  forall n m:Z, if Zge_bool n m then (n >= m) else (n < m).
Proof.
  intros x y; unfold Zge_bool, Zge, Zlt in |- *.
  case (x ?= y); auto; discriminate.
Qed.

Lemma Zgt_cases :
  forall n m:Z, if Zgt_bool n m then (n > m) else (n <= m).
Proof.
  intros x y; unfold Zgt_bool, Zgt, Zle in |- *.
  case (x ?= y); auto; discriminate.
Qed.

(** Lemmas on [Zle_bool] used in contrib/graphs *)

Lemma Zle_bool_imp_le : forall n m:Z, Zle_bool n m = true -> (n <= m).
Proof.
  unfold Zle_bool, Zle in |- *. intros x y. unfold not in |- *.
  case (x ?= y); intros; discriminate.
Qed.

Lemma Zle_imp_le_bool : forall n m:Z, (n <= m) -> Zle_bool n m = true.
Proof.
  unfold Zle, Zle_bool in |- *. intros x y. case (x ?= y); trivial. intro. elim (H (refl_equal _)).
Qed.

Lemma Zle_bool_refl : forall n:Z, Zle_bool n n = true.
Proof.
  intro. apply Zle_imp_le_bool. apply Zeq_le. reflexivity.
Qed.

Lemma Zle_bool_antisym :
  forall n m:Z, Zle_bool n m = true -> Zle_bool m n = true -> n = m.
Proof.
  intros. apply Zle_antisym. apply Zle_bool_imp_le. assumption.
  apply Zle_bool_imp_le. assumption.
Qed.

Lemma Zle_bool_trans :
  forall n m p:Z,
    Zle_bool n m = true -> Zle_bool m p = true -> Zle_bool n p = true.
Proof.
  intros x y z; intros. apply Zle_imp_le_bool. apply Zle_trans with (m := y). apply Zle_bool_imp_le. assumption.
  apply Zle_bool_imp_le. assumption.
Qed.

Definition Zle_bool_total :
  forall x y:Z, {Zle_bool x y = true} + {Zle_bool y x = true}.
Proof.
  intros x y; intros. unfold Zle_bool in |- *. cut ((x ?= y) = Gt <-> (y ?= x) = Lt).
  case (x ?= y). left. reflexivity.
  left. reflexivity.
  right. rewrite (proj1 H (refl_equal _)). reflexivity.
  apply Zcompare_Gt_Lt_antisym.
Defined.

Lemma Zle_bool_plus_mono :
  forall n m p q:Z,
    Zle_bool n m = true ->
    Zle_bool p q = true -> Zle_bool (n + p) (m + q) = true.
Proof.
  intros. apply Zle_imp_le_bool. apply Zplus_le_compat. apply Zle_bool_imp_le. assumption.
  apply Zle_bool_imp_le. assumption.
Qed.

Lemma Zone_pos : Zle_bool 1 0 = false.
Proof.
  reflexivity.
Qed.

Lemma Zone_min_pos : forall n:Z, Zle_bool n 0 = false -> Zle_bool 1 n = true.
Proof.
  intros x; intros. apply Zle_imp_le_bool. change (Zsucc 0 <= x) in |- *. apply Zgt_le_succ. generalize H.
  unfold Zle_bool, Zgt in |- *. case (x ?= 0). intro H0. discriminate H0.
  intro H0. discriminate H0.
  reflexivity.
Qed.

(** Properties in term of [iff] *)

Lemma Zle_is_le_bool : forall n m:Z, (n <= m) <-> Zle_bool n m = true.
Proof.
  intros. split. intro. apply Zle_imp_le_bool. assumption.
  intro. apply Zle_bool_imp_le. assumption.
Qed.

Lemma Zge_is_le_bool : forall n m:Z, (n >= m) <-> Zle_bool m n = true.
Proof.
  intros. split. intro. apply Zle_imp_le_bool. apply Zge_le. assumption.
  intro. apply Zle_ge. apply Zle_bool_imp_le. assumption.
Qed.

Lemma Zlt_is_lt_bool : forall n m:Z, (n < m) <-> Zlt_bool n m = true.
Proof.
intros n m; unfold Zlt_bool, Zlt.
destruct (n ?= m); simpl; split; now intro.
Qed.

Lemma Zgt_is_gt_bool : forall n m:Z, (n > m) <-> Zgt_bool n m = true.
Proof.
intros n m; unfold Zgt_bool, Zgt.
destruct (n ?= m); simpl; split; now intro.
Qed.

Lemma Zlt_is_le_bool :
  forall n m:Z, (n < m) <-> Zle_bool n (m - 1) = true.
Proof.
  intros x y. split. intro. apply Zle_imp_le_bool. apply Zlt_succ_le. rewrite (Zsucc_pred y) in H.
  assumption.
  intro. rewrite (Zsucc_pred y). apply Zle_lt_succ. apply Zle_bool_imp_le. assumption.
Qed.

Lemma Zgt_is_le_bool :
  forall n m:Z, (n > m) <-> Zle_bool m (n - 1) = true.
Proof.
  intros x y. apply iff_trans with (y < x). split. exact (Zgt_lt x y).
  exact (Zlt_gt y x).
  exact (Zlt_is_le_bool y x).
Qed.

Lemma Zeq_is_eq_bool : forall x y, x = y <-> Zeq_bool x y = true.
Proof.
  intros; unfold Zeq_bool.
  generalize (Zcompare_Eq_iff_eq x y); destruct Zcompare; intuition;
   try discriminate.
Qed.

Lemma Zeq_bool_eq : forall x y, Zeq_bool x y = true -> x = y.
Proof.
  intros x y H; apply <- Zeq_is_eq_bool; auto.
Qed.

Lemma Zeq_bool_neq : forall x y, Zeq_bool x y = false -> x <> y.
Proof.
  unfold Zeq_bool; red ; intros; subst.
  rewrite Zcompare_refl in H.
  discriminate.
Qed.

Lemma Zeq_bool_if : forall x y, if Zeq_bool x y then x=y else x<>y.
Proof.
  intros. generalize (Zeq_bool_eq x y)(Zeq_bool_neq x y).
  destruct Zeq_bool; auto.
Qed.