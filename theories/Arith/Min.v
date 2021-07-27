(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * THIS FILE IS DEPRECATED. Use [PeanoNat.Nat] or [Arith.Arith_base] instead. *)

Require Import PeanoNat.


Local Open Scope nat_scope.
Implicit Types m n p : nat.

#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min instead.")]
Notation min := Nat.min (only parsing).

#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_0_l instead.")]
Notation min_0_l := Nat.min_0_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_0_r instead.")]
Notation min_0_r := Nat.min_0_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.succ_min_distr instead.")]
Notation succ_min_distr := Nat.succ_min_distr (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.add_min_distr_l instead.")]
Notation plus_min_distr_l := Nat.add_min_distr_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.add_min_distr_r instead.")]
Notation plus_min_distr_r := Nat.add_min_distr_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_case_strong instead.")]
Notation min_case_strong := Nat.min_case_strong (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_spec instead.")]
Notation min_spec := Nat.min_spec (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_dec instead.")]
Notation min_dec := Nat.min_dec (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_case instead.")]
Notation min_case := Nat.min_case (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_id instead.")]
Notation min_idempotent := Nat.min_id (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_assoc instead.")]
Notation min_assoc := Nat.min_assoc (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_comm instead.")]
Notation min_comm := Nat.min_comm (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_l instead.")]
Notation min_l := Nat.min_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_r instead.")]
Notation min_r := Nat.min_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.le_min_l instead.")]
Notation le_min_l := Nat.le_min_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.le_min_r instead.")]
Notation le_min_r := Nat.le_min_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_glb_l instead.")]
Notation min_glb_l := Nat.min_glb_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_glb_r instead.")]
Notation min_glb_r := Nat.min_glb_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_glb instead.")]
Notation min_glb := Nat.min_glb (only parsing).

(* begin hide *)
(* Compatibility *)
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.min_case instead.")]
Notation min_case2 := Nat.min_case (only parsing).
#[deprecated(since="8.16",note="The Arith.Min file is obsolete. Use Nat.succ_min_distr instead.")]
Notation min_SS := Nat.succ_min_distr (only parsing).
(* end hide *)
