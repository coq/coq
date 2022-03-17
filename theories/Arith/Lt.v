(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Strict order on natural numbers. *)

(** * This file is OBSOLETE, see [Arith_base] instead. *)

Require Export Arith_prebase.


(** * Irreflexivity *)

#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_irrefl instead.")]
Notation lt_irrefl := Nat.lt_irrefl (only parsing). (* ~ x < x *)

(** * Relationship between [le] and [lt] *)

#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.le_succ_l instead.")]
Notation lt_le_S := Arith_prebase.lt_le_S_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.lt_succ_r instead.")]
Notation lt_n_Sm_le := Arith_prebase.lt_n_Sm_le_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.lt_succ_r instead.")]
Notation le_lt_n_Sm := Arith_prebase.le_lt_n_Sm_stt (only parsing).
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.le_ngt instead.")]
Notation le_not_lt := Arith_prebase.le_not_lt_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.lt_nge instead.")]
Notation lt_not_le := Arith_prebase.lt_not_le_stt.

(** * Asymmetry *)

#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_asymm instead.")]
Notation lt_asym := Nat.lt_asymm (only parsing). (* n<m -> ~m<n *)

(** * Order and 0 *)

#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_0_succ instead.")]
Notation lt_0_Sn := Nat.lt_0_succ (only parsing). (* 0 < S n *)
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.nlt_0_r instead.")]
Notation lt_n_0 := Nat.nlt_0_r (only parsing). (* ~ n < 0 *)
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.neq_0_lt_0 (together with Nat.neq_sym) instead.")]
Notation neq_0_lt := Arith_prebase.neq_0_lt_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.neq_0_lt_0 (together with Nat.neq_sym) instead.")]
Notation lt_0_neq := Arith_prebase.lt_0_neq_stt.

(** * Order and successor *)

#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_succ_diag_r instead.")]
Notation lt_n_Sn := Nat.lt_succ_diag_r (only parsing). (* n < S n *)
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_lt_succ_r instead.")]
Notation lt_S := Nat.lt_lt_succ_r (only parsing). (* n < m -> n < S m *)
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.succ_lt_mono instead.")]
Notation lt_n_S := Arith_prebase.lt_n_S_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.succ_lt_mono instead.")]
Notation lt_S_n := Arith_prebase.lt_S_n_stt.

(** * Predecessor *)

#[local]
Definition S_pred_stt := fun n m Hlt => eq_sym (Nat.lt_succ_pred m n Hlt).
Opaque S_pred_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_succ_pred (with symmetry of equality) instead.")]
Notation S_pred := S_pred_stt.
#[local]
Definition S_pred_pos_stt := fun n Hlt => eq_sym (Nat.lt_succ_pred 0 n Hlt).
Opaque S_pred_pos_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_succ_pred (with symmetry of equality) instead.")]
Notation S_pred_pos := S_pred_pos_stt (only parsing).
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.lt_succ_lt_pred instead.")]
Notation lt_pred := Arith_prebase.lt_pred_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_pred_l (together with Nat.neq_0_lt_0) instead.")]
Notation lt_pred_n_n := Arith_prebase.lt_pred_n_n_stt.

(** * Transitivity properties *)

#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_trans instead.")]
Notation lt_trans := Nat.lt_trans (only parsing).
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_le_trans instead.")]
Notation lt_le_trans := Nat.lt_le_trans (only parsing).
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.le_lt_trans instead.")]
Notation le_lt_trans := Nat.le_lt_trans (only parsing).

(** * Large = strict or equal *)

#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_eq_cases instead.")]
Notation le_lt_or_eq_iff := Nat.lt_eq_cases (only parsing).
#[local]
Definition le_lt_or_eq_stt := fun n m => proj1 (Nat.lt_eq_cases n m).
Opaque le_lt_or_eq_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.lt_eq_cases instead.")]
Notation le_lt_or_eq := le_lt_or_eq_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_le_incl instead.")]
Notation lt_le_weak := Nat.lt_le_incl (only parsing).

(** * Dichotomy *)

#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.le_gt_cases instead.")]
Notation le_or_lt := Nat.le_gt_cases (only parsing). (* n <= m \/ m < n *)
#[local]
Definition nat_total_order_stt := fun n m => proj1 (Nat.lt_gt_cases n m).
Opaque nat_total_order_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.lt_gt_cases instead.")]
Notation nat_total_order := nat_total_order_stt.

(* begin hide *)
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.lt_0_succ instead.")]
Notation lt_O_Sn := Nat.lt_0_succ (only parsing).
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.neq_0_lt_0 (together with Nat.neq_sym) instead.")]
Notation neq_O_lt := Arith_prebase.neq_0_lt_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use the bidirectional version Nat.neq_0_lt_0 (together with Nat.neq_sym) instead.")]
Notation lt_O_neq := Arith_prebase.lt_0_neq_stt.
#[deprecated(since="8.16",note="The Arith.Lt file is obsolete. Use Nat.nlt_0_r instead.")]
Notation lt_n_O := Nat.nlt_0_r (only parsing).
(* end hide *)

Require Import Le.
