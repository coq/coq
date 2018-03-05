(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinInt.
Require Import Zeven.
Require Import Zorder.
Require Import Zcompare.
Require Import ZArith_dec.
Require Import Sumbool.

Local Open Scope Z_scope.

(** * Boolean operations from decidability of order *)
(** The decidability of equality and order relations over
    type [Z] gives some boolean functions with the adequate specification. *)

Definition Z_lt_ge_bool (x y:Z) := bool_of_sumbool (Z_lt_ge_dec x y).
Definition Z_ge_lt_bool (x y:Z) := bool_of_sumbool (Z_ge_lt_dec x y).

Definition Z_le_gt_bool (x y:Z) := bool_of_sumbool (Z_le_gt_dec x y).
Definition Z_gt_le_bool (x y:Z) := bool_of_sumbool (Z_gt_le_dec x y).

Definition Z_eq_bool (x y:Z) := bool_of_sumbool (Z.eq_dec x y).
Definition Z_noteq_bool (x y:Z) := bool_of_sumbool (Z_noteq_dec x y).

Definition Zeven_odd_bool (x:Z) := bool_of_sumbool (Zeven_odd_dec x).

(**********************************************************************)
(** * Boolean comparisons of binary integers *)

Notation Zle_bool := Z.leb (only parsing).
Notation Zge_bool := Z.geb (only parsing).
Notation Zlt_bool := Z.ltb (only parsing).
Notation Zgt_bool := Z.gtb (only parsing).

(** We now provide a direct [Z.eqb] that doesn't refer to [Z.compare].
   The old [Zeq_bool] is kept for compatibility. *)

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

Lemma Zle_cases n m : if n <=? m then n <= m else n > m.
Proof.
 case Z.leb_spec; now Z.swap_greater.
Qed.

Lemma Zlt_cases n m : if n <? m then n < m else n >= m.
Proof.
 case Z.ltb_spec; now Z.swap_greater.
Qed.

Lemma Zge_cases n m : if n >=? m then n >= m else n < m.
Proof.
 rewrite Z.geb_leb. case Z.leb_spec; now Z.swap_greater.
Qed.

Lemma Zgt_cases n m : if n >? m then n > m else n <= m.
Proof.
 rewrite Z.gtb_ltb. case Z.ltb_spec; now Z.swap_greater.
Qed.

(** Lemmas on [Z.leb] used in contrib/graphs *)

Lemma Zle_bool_imp_le n m : (n <=? m) = true -> (n <= m).
Proof.
 apply Z.leb_le.
Qed.

Lemma Zle_imp_le_bool n m : (n <= m) -> (n <=? m) = true.
Proof.
 apply Z.leb_le.
Qed.

Notation Zle_bool_refl := Z.leb_refl (only parsing).

Lemma Zle_bool_antisym n m :
 (n <=? m) = true -> (m <=? n) = true -> n = m.
Proof.
 rewrite !Z.leb_le. apply Z.le_antisymm.
Qed.

Lemma Zle_bool_trans n m p :
 (n <=? m) = true -> (m <=? p) = true -> (n <=? p) = true.
Proof.
 rewrite !Z.leb_le. apply Z.le_trans.
Qed.

Definition Zle_bool_total x y :
  { x <=? y = true } + { y <=? x = true }.
Proof.
 case_eq (x <=? y); intros H.
 - left; trivial.
 - right. apply Z.leb_gt in H. now apply Z.leb_le, Z.lt_le_incl.
Defined.

Lemma Zle_bool_plus_mono n m p q :
 (n <=? m) = true ->
 (p <=? q) = true ->
 (n + p <=? m + q) = true.
Proof.
 rewrite !Z.leb_le. apply Z.add_le_mono.
Qed.

Lemma Zone_pos : 1 <=? 0 = false.
Proof.
 reflexivity.
Qed.

Lemma Zone_min_pos n : (n <=? 0) = false -> (1 <=? n) = true.
Proof.
 rewrite Z.leb_le, Z.leb_gt. apply Z.le_succ_l.
Qed.

(** Properties in term of [iff] *)

Lemma Zle_is_le_bool n m : (n <= m) <-> (n <=? m) = true.
Proof.
 symmetry. apply Z.leb_le.
Qed.

Lemma Zge_is_le_bool n m : (n >= m) <-> (m <=? n) = true.
Proof.
 Z.swap_greater. symmetry. apply Z.leb_le.
Qed.

Lemma Zlt_is_lt_bool n m : (n < m) <-> (n <? m) = true.
Proof.
 symmetry. apply Z.ltb_lt.
Qed.

Lemma Zgt_is_gt_bool n m : (n > m) <-> (n >? m) = true.
Proof.
 Z.swap_greater. rewrite Z.gtb_ltb. symmetry. apply Z.ltb_lt.
Qed.

Lemma Zlt_is_le_bool n m : (n < m) <-> (n <=? m - 1) = true.
Proof.
 rewrite Z.leb_le. apply Z.lt_le_pred.
Qed.

Lemma Zgt_is_le_bool n m : (n > m) <-> (m <=? n - 1) = true.
Proof.
 Z.swap_greater. rewrite Z.leb_le. apply Z.lt_le_pred.
Qed.

(** Properties of the deprecated [Zeq_bool] *)

Lemma Zeq_is_eq_bool x y : x = y <-> Zeq_bool x y = true.
Proof.
 unfold Zeq_bool.
 rewrite <- Z.compare_eq_iff. destruct Z.compare; now split.
Qed.

Lemma Zeq_bool_eq x y : Zeq_bool x y = true -> x = y.
Proof.
 apply Zeq_is_eq_bool.
Qed.

Lemma Zeq_bool_neq x y : Zeq_bool x y = false -> x <> y.
Proof.
 rewrite Zeq_is_eq_bool; now destruct Zeq_bool.
Qed.

Lemma Zeq_bool_if x y : if Zeq_bool x y then x=y else x<>y.
Proof.
 generalize (Zeq_bool_eq x y) (Zeq_bool_neq x y).
 destruct Zeq_bool; auto.
Qed.
