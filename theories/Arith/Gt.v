(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Theorems about [gt] in [nat]. *)

(** * This file is OBSOLETE, see [Arith_base] instead. *)

Require Export Arith_prebase.


Local Open Scope nat_scope.

(** * Order and successor *)

#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.lt_0_succ instead.")]
Notation gt_Sn_O := Arith_prebase.gt_Sn_O_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.lt_succ_diag_r instead.")]
Notation gt_Sn_n := Arith_prebase.gt_Sn_n_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.succ_lt_mono instead.")]
Notation gt_n_S := Arith_prebase.gt_n_S_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.succ_lt_mono instead.")]
Notation gt_S_n := Arith_prebase.gt_S_n_stt.
#[local]
Definition gt_S_stt : forall n m, S n > m -> n > m \/ m = n := fun n m Hgt => proj1 (Nat.lt_eq_cases m n) (proj2 (Nat.succ_le_mono m n) Hgt).
Opaque gt_S_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.lt_eq_cases (together with Nat.succ_le_mono) instead.")]
Notation gt_S := gt_S_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.lt_succ_lt_pred instead.")]
Notation gt_pred := Arith_prebase.gt_pred_stt.

(** * Irreflexivity *)

#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.lt_irrefl instead.")]
Notation gt_irrefl := Arith_prebase.gt_irrefl_stt.

(** * Asymmetry *)

#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.lt_asymm instead.")]
Notation gt_asym := Arith_prebase.gt_asym_stt.

(** * Relating strict and large orders *)

#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.le_ngt instead.")]
Notation le_not_gt := Arith_prebase.le_not_gt_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.lt_nge instead.")]
Notation gt_not_le := Arith_prebase.gt_not_le_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.le_succ_l instead.")]
Notation le_S_gt := Arith_prebase.le_S_gt_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.succ_le_mono instead.")]
Notation gt_S_le := Arith_prebase.gt_S_le_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.le_succ_l instead.")]
Notation gt_le_S := Arith_prebase.gt_le_S_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.succ_le_mono instead.")]
Notation le_gt_S := Arith_prebase.le_gt_S_stt.

(** * Transitivity *)

#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.lt_le_trans instead.")]
Notation le_gt_trans := Arith_prebase.le_gt_trans_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.le_lt_trans instead.")]
Notation gt_le_trans := Arith_prebase.gt_le_trans_stt.
#[local]
Definition gt_trans_stt : forall n m p, n > m -> m > p -> n > p := fun n m p Hgt1 Hgt2 => Nat.lt_trans p m n Hgt2 Hgt1.
Opaque gt_trans_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.lt_trans instead.")]
Notation gt_trans := gt_trans_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.lt_le_trans (together with Nat.succ_le_mono) instead.")]
Notation gt_trans_S := Arith_prebase.gt_trans_S_stt.

(** * Comparison to 0 *)

#[local]
Definition gt_0_eq_stt n : n > 0 \/ 0 = n.
Proof. destruct (Nat.eq_0_gt_0_cases n); auto. Qed.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.eq_0_gt_0_cases (and commutativity of disjunction) instead.")]
Notation gt_0_eq := gt_0_eq_stt.
(* begin hide *)
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use Nat.eq_0_gt_0_cases (and commutativity of disjunction) instead.")]
Notation gt_O_eq := gt_0_eq_stt (only parsing).
(* end hide *)

(** * Simplification and compatibility *)

#[local]
Definition plus_gt_reg_l_stt : forall n m p, p + n > p + m -> n > m := fun n m p Hgt => proj2 (Nat.add_lt_mono_l m n p) Hgt.
Opaque plus_gt_reg_l_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.add_lt_mono_l instead.")]
Notation plus_gt_reg_l := plus_gt_reg_l_stt.
#[deprecated(since="8.16",note="The Arith.Gt file is obsolete. Use the bidirectional version Nat.add_lt_mono_l instead.")]
Notation plus_gt_compat_l := Arith_prebase.plus_gt_compat_l_stt.

Require Import Le Lt Plus.
