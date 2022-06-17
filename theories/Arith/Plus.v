(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of addition. *)

(** * This file is OBSOLETE, see [Arith_base] instead. *)

Require Export Arith_prebase.


Local Open Scope nat_scope.

(** * Neutrality of 0, commutativity, associativity *)

#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_0_l instead.")]
Notation plus_0_l := Nat.add_0_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_0_r instead.")]
Notation plus_0_r := Nat.add_0_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_comm instead.")]
Notation plus_comm := Nat.add_comm (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_assoc instead.")]
Notation plus_assoc := Nat.add_assoc (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_shuffle3 instead.")]
Notation plus_permute := Nat.add_shuffle3 (only parsing).
#[local]
Definition plus_Snm_nSm_stt : forall n m, S n + m = n + S m := Peano.plus_n_Sm.
Opaque plus_Snm_nSm_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_succ_r (and symmetry of equality) instead.")]
Notation plus_Snm_nSm := plus_Snm_nSm_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_assoc (and symmetry of equality) instead.")]
Notation plus_assoc_reverse := Arith_prebase.plus_assoc_reverse_stt.

(** * Simplification *)

#[local]
Definition plus_reg_l_stt := fun n m p => proj1 (Nat.add_cancel_l n m p).
Opaque plus_reg_l_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the bidirectional version Nat.add_cancel_l instead.")]
Notation plus_reg_l := plus_reg_l_stt.
#[local]
Definition plus_le_reg_l_stt := fun n m p => proj2 (Nat.add_le_mono_l n m p).
Opaque plus_le_reg_l_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the bidirectional version Nat.add_le_mono_l instead.")]
Notation plus_le_reg_l := plus_le_reg_l_stt.
#[local]
Definition plus_lt_reg_l_stt := fun n m p => proj2 (Nat.add_lt_mono_l n m p).
Opaque plus_lt_reg_l_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the bidirectional version Nat.add_lt_mono_l instead.")]
Notation plus_lt_reg_l := plus_lt_reg_l_stt.

(** * Compatibility with order *)

#[local]
Definition plus_le_compat_l_stt := fun n m p => proj1 (Nat.add_le_mono_l n m p).
Opaque plus_le_compat_l_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the bidirectional version Nat.add_le_mono_l instead.")]
Notation plus_le_compat_l := plus_le_compat_l_stt.
#[local]
Definition plus_le_compat_r_stt := fun n m p => proj1 (Nat.add_le_mono_r n m p).
Opaque plus_le_compat_r_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the bidirectional version Nat.add_le_mono_r instead.")]
Notation plus_le_compat_r := plus_le_compat_r_stt.
#[local]
Definition plus_lt_compat_l_stt := fun n m p => proj1 (Nat.add_lt_mono_l n m p).
Opaque plus_lt_compat_l_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the bidirectional version Nat.add_lt_mono_l instead.")]
Notation plus_lt_compat_l := plus_lt_compat_l_stt.
#[local]
Definition plus_lt_compat_r_stt := fun n m p => proj1 (Nat.add_lt_mono_r n m p).
Opaque plus_lt_compat_r_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the bidirectional version Nat.add_lt_mono_r instead.")]
Notation plus_lt_compat_r := plus_lt_compat_r_stt.

#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_le_mono instead.")]
Notation plus_le_compat := Nat.add_le_mono (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_le_lt_mono instead.")]
Notation plus_le_lt_compat := Nat.add_le_lt_mono (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_lt_le_mono instead.")]
Notation plus_lt_le_compat := Nat.add_lt_le_mono (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_lt_mono instead.")]
Notation plus_lt_compat := Nat.add_lt_mono (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.le_add_r instead.")]
Notation le_plus_l := Nat.le_add_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.le_add_l (with arguments reversed) instead.")]
Notation le_plus_r := Arith_prebase.le_plus_r_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.le_add_r (together with Nat.le_trans) instead.")]
Notation le_plus_trans := Arith_prebase.le_plus_trans_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.le_add_r (together with Nat.lt_le_trans) instead.")]
Notation lt_plus_trans := Arith_prebase.lt_plus_trans_stt.

(** * Inversion lemmas *)

#[local]
Definition plus_is_O_stt := fun n m => proj1 (Nat.eq_add_0 n m).
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the bidirectional version Nat.eq_add_0 instead.")]
Notation plus_is_O := plus_is_O_stt.

#[local]
Definition plus_is_one_stt m n :
  m + n = 1 -> {m = 0 /\ n = 1} + {m = 1 /\ n = 0}.
Proof.
  destruct m as [| m]; auto.
  destruct m; auto.
  discriminate.
Defined.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use the Prop version Nat.eq_add_1 instead.")]
Notation plus_is_one := plus_is_one_stt.

(** * Derived properties *)

#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.add_shuffle1 instead.")]
Notation plus_permute_2_in_4 := Nat.add_shuffle1 (only parsing).

(** * Discrimination *)

#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.succ_add_discr instead.")]
Notation succ_plus_discr := Nat.succ_add_discr (only parsing).
#[local]
Definition n_SSn_stt : forall n, n <> S (S n) := fun n => Nat.succ_add_discr 1 n.
Opaque n_SSn_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use (Nat.succ_add_discr 1) instead.")]
Notation n_SSn := n_SSn_stt.
#[local]
Definition n_SSSn_stt : forall n, n <> S (S (S n)) := fun n => Nat.succ_add_discr 2 n.
Opaque n_SSSn_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use (Nat.succ_add_discr 2) instead.")]
Notation n_SSSn := n_SSSn_stt.
#[local]
Definition n_SSSSn_stt : forall n, n <> S (S (S (S n))) := fun n => Nat.succ_add_discr 3 n.
Opaque n_SSSSn_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use (Nat.succ_add_discr 3) instead.")]
Notation n_SSSSn := n_SSSSn_stt.

(** * Tail-recursive [plus] *)
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.tail_add instead.")]
Notation tail_plus := Nat.tail_add (only parsing).
#[local]
Definition plus_tail_plus_stt := fun n m => eq_sym (Nat.tail_add_spec n m).
Opaque plus_tail_plus_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete. Use Nat.tail_add_spec (with symmetry of equality) instead.")]
Notation plus_tail_plus := plus_tail_plus_stt.

Require Import Le Lt.
