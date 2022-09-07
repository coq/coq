(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of subtraction between natural numbers. *)

(** * This file is OBSOLETE, see [Arith_base] instead. *)

Require Export Arith_prebase.


Local Open Scope nat_scope.

(** * 0 is right neutral *)

#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_0_r (and symmetry of equality) instead.")]
Notation minus_n_O := Arith_prebase.minus_n_O_stt.

(** * Permutation with successor *)

#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_succ_l (and symmetry of equality) instead.")]
Notation minus_Sn_m := Arith_prebase.minus_Sn_m_stt.
#[local]
Definition pred_of_minus_stt := fun n => eq_sym (Nat.sub_1_r n).
Opaque pred_of_minus_stt.
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_1_r (and symmetry of equality) instead.")]
Notation pred_of_minus:= pred_of_minus_stt.

(** * Diagonal *)

#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_diag instead.")]
Notation minus_diag := Nat.sub_diag (only parsing). (* n - n = 0 *)
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_diag (and symmetry of equality) instead.")]
Notation minus_diag_reverse := Arith_prebase.minus_diag_reverse_stt.
#[local]
Definition minus_n_n_stt := fun n => eq_sym (Nat.sub_diag n).
Opaque minus_n_n_stt.
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_diag (and symmetry of equality) instead.")]
Notation minus_n_n := minus_n_n_stt.

(** * Simplification *)

#[deprecated(since="8.16",note="The Arith.Minus file is obsolete.")]
Notation minus_plus_simpl_l_reverse := Arith_prebase.minus_plus_simpl_l_reverse_stt.

(** * Relation with plus *)

#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.add_sub_eq_l (and symmetry of equality) instead.")]
Notation plus_minus := Arith_prebase.plus_minus_stt.
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.add_sub (together with Nat.add_comm) instead.")]
Notation minus_plus := Arith_prebase.minus_plus_stt.
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_add (together with Nat.add_comm) instead.")]
Notation le_plus_minus_r := Arith_prebase.le_plus_minus_r_stt.
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_add (together with Nat.add_comm) instead.")]
Notation le_plus_minus := Arith_prebase.le_plus_minus_stt.

(** * Relation with order *)

#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_le_mono_r instead.")]
Notation minus_le_compat_r := Nat.sub_le_mono_r (only parsing). (* n <= m -> n - p <= m - p. *)
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_le_mono_l instead.")]
Notation minus_le_compat_l := Nat.sub_le_mono_l (only parsing). (* n <= m -> p - m <= p - n. *)
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.le_sub_l instead.")]
Notation le_minus := Nat.le_sub_l (only parsing). (* n - m <= n *)
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_lt instead.")]
Notation lt_minus := Nat.sub_lt (only parsing). (* m <= n -> 0 < m -> n-m < n *)
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use the bidirectional version (Nat.lt_add_lt_sub_r 0) instead.")]
Notation lt_O_minus_lt := Arith_prebase.lt_O_minus_lt_stt.
#[local]
Definition not_le_minus_0_stt := fun n m Hn => proj2 (Nat.sub_0_le n m) (Nat.lt_le_incl _ _ (proj2 (Nat.lt_nge _ _) Hn)).
Opaque not_le_minus_0_stt.
#[deprecated(since="8.16",note="The Arith.Minus file is obsolete. Use Nat.sub_0_le (together with Nat.lt_nge and Nat.lt_le_incl) instead.")]
Notation not_le_minus_0 := not_le_minus_0_stt.

Require Import Lt Le.
