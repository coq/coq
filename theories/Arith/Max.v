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

#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max instead.")]
Notation max := Nat.max (only parsing).

#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_0_l instead.")]
Notation max_0_l := Nat.max_0_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_0_r instead.")]
Notation max_0_r := Nat.max_0_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.succ_max_distr instead.")]
Notation succ_max_distr := Nat.succ_max_distr (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.add_max_distr_l instead.")]
Notation plus_max_distr_l := Nat.add_max_distr_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.add_max_distr_r instead.")]
Notation plus_max_distr_r := Nat.add_max_distr_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_case_strong instead.")]
Notation max_case_strong := Nat.max_case_strong (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_spec instead.")]
Notation max_spec := Nat.max_spec (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_dec instead.")]
Notation max_dec := Nat.max_dec (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_case instead.")]
Notation max_case := Nat.max_case (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_id instead.")]
Notation max_idempotent := Nat.max_id (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_assoc instead.")]
Notation max_assoc := Nat.max_assoc (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_comm instead.")]
Notation max_comm := Nat.max_comm (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_l instead.")]
Notation max_l := Nat.max_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_r instead.")]
Notation max_r := Nat.max_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.le_max_l instead.")]
Notation le_max_l := Nat.le_max_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.le_max_r instead.")]
Notation le_max_r := Nat.le_max_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_lub_l instead.")]
Notation max_lub_l := Nat.max_lub_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_lub_r instead.")]
Notation max_lub_r := Nat.max_lub_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_lub instead.")]
Notation max_lub := Nat.max_lub (only parsing).

(* begin hide *)
(* Compatibility *)
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.max_case instead.")]
Notation max_case2 := Nat.max_case (only parsing).
#[deprecated(since="8.16",note="The Arith.Max file is obsolete. Use Nat.succ_max_distr instead.")]
Notation max_SS := Nat.succ_max_distr (only parsing).
(* end hide *)

#[global]
Hint Resolve Nat.max_l Nat.max_r Nat.le_max_l Nat.le_max_r: arith.
#[global]
Hint Resolve Nat.min_l Nat.min_r Nat.le_min_l Nat.le_min_r: arith.
