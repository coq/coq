(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Properties of multiplication. *)

(** * This file is OBSOLETE, see [Arith_base] instead. *)

Require Export Arith_prebase.


Local Open Scope nat_scope.

(** * [nat] is a semi-ring *)

(** ** Zero property *)

#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_0_l instead.")]
Notation mult_0_l := Nat.mul_0_l (only parsing). (* 0 * n = 0 *)
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_0_r instead.")]
Notation mult_0_r := Nat.mul_0_r (only parsing). (* n * 0 = 0 *)

(** ** 1 is neutral *)

#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_1_l instead.")]
Notation mult_1_l := Nat.mul_1_l (only parsing). (* 1 * n = n *)
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_1_r instead.")]
Notation mult_1_r := Nat.mul_1_r (only parsing). (* n * 1 = n *)

(** ** Commutativity *)

#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_comm instead.")]
Notation mult_comm := Nat.mul_comm (only parsing). (* n * m = m * n *)

(** ** Distributivity *)

#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_add_distr_r instead.")]
Notation mult_plus_distr_r :=
  Nat.mul_add_distr_r (only parsing). (* (n+m)*p = n*p + m*p *)
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_add_distr_l instead.")]
Notation mult_plus_distr_l :=
  Nat.mul_add_distr_l (only parsing). (* n*(m+p) = n*m + n*p *)
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_sub_distr_r instead.")]
Notation mult_minus_distr_r :=
  Nat.mul_sub_distr_r (only parsing). (* (n-m)*p = n*p - m*p *)
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_sub_distr_l instead.")]
Notation mult_minus_distr_l :=
  Nat.mul_sub_distr_l (only parsing). (* n*(m-p) = n*m - n*p *)

(** ** Associativity *)

#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_assoc instead.")]
Notation mult_assoc := Nat.mul_assoc (only parsing). (* n*(m*p)=n*m*p *)
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_assoc (with symmetry of equality) instead.")]
Notation mult_assoc_reverse := Arith_prebase.mult_assoc_reverse_stt.

(** ** Inversion lemmas *)

#[local]
Definition mult_is_O_stt := fun n m Heq => proj1 (Nat.eq_mul_0 n m) Heq.
Opaque mult_is_O_stt.
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use the bidirectional version Nat.eq_mul_0 instead.")]
Notation mult_is_O := mult_is_O_stt.
#[local]
Definition mult_is_one_stt := fun n m Heq => proj1 (Nat.eq_mul_1 n m) Heq.
Opaque mult_is_one_stt.
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use the bidirectional version Nat.eq_mul_1 instead.")]
Notation mult_is_one := mult_is_one_stt.

(** ** Multiplication and successor *)

#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_succ_l instead.")]
Notation mult_succ_l := Nat.mul_succ_l (only parsing). (* S n * m = n * m + m *)
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_succ_r instead.")]
Notation mult_succ_r := Nat.mul_succ_r (only parsing). (* n * S m = n * m + n *)

(** * Compatibility with orders *)

#[deprecated(since="8.16",note="The Arith.Mult file is obsolete.")]
Notation mult_O_le := Arith_prebase.mult_O_le_stt.
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_le_mono_l instead.")]
Notation mult_le_compat_l := Nat.mul_le_mono_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_le_mono_r instead.")]
Notation mult_le_compat_r := Nat.mul_le_mono_r (only parsing).
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.mul_le_mono instead.")]
Notation mult_le_compat := Nat.mul_le_mono (only parsing).
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use the bidirectional version (Nat.mul_lt_mono_pos_l (S _)) (together with Nat.lt_0_succ) instead.")]
Notation mult_S_lt_compat_l := Arith_prebase.mult_S_lt_compat_l_stt.
#[local]
Definition mult_lt_compat_l_stt := fun n m p Hlt Hp => proj1 (Nat.mul_lt_mono_pos_l p n m Hp) Hlt.
Opaque mult_lt_compat_l_stt.
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use the bidirectional version Nat.mul_lt_mono_pos_l instead.")]
Notation mult_lt_compat_l := mult_lt_compat_l_stt.
#[local]
Definition mult_lt_compat_r_stt := fun n m p Hlt Hp => proj1 (Nat.mul_lt_mono_pos_r p n m Hp) Hlt.
Opaque mult_lt_compat_r_stt.
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use the bidirectional version Nat.mul_lt_mono_pos_r instead.")]
Notation mult_lt_compat_r := mult_lt_compat_r_stt.
#[local]
Definition mult_S_le_reg_l_stt := fun n m p Hle => proj2 (Nat.mul_le_mono_pos_l m p (S n) (Nat.lt_0_succ n)) Hle.
Opaque mult_S_le_reg_l_stt.
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use the bidirectional version (Nat.mul_le_mono_pos_l _ _ (S _)) (together with Nat.lt_0_succ) instead.")]
Notation mult_S_le_reg_l := mult_S_le_reg_l_stt.

(** * n|->2*n and n|->2n+1 have disjoint image *)

#[local]
Definition odd_even_lem_stt p q : 2 * p + 1 <> 2 * q.
Proof.
 intro. apply (Nat.Even_Odd_False (2*q)).
 - now exists q.
 - now exists p.
Qed.
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.Even_Odd_False instead.")]
Notation odd_even_lem := odd_even_lem_stt.

(** * Tail-recursive [mult] *)

#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.tail_mul instead.")]
Notation tail_mult := Nat.tail_mul (only parsing).
#[local]
Definition mult_tail_mult_stt := fun n m => eq_sym (Nat.tail_mul_spec n m).
Opaque mult_tail_mult_stt.
#[deprecated(since="8.16",note="The Arith.Mult file is obsolete. Use Nat.tail_mul_spec (with symmetry of equality) instead.")]
Notation mult_tail_mult := mult_tail_mult_stt.
#[deprecated(since="8.16",note="The Arith.Plus file is obsolete.")]
Ltac tail_simpl :=
  repeat rewrite Nat.tail_add_spec; repeat rewrite Nat.tail_mul_spec; simpl.

Require Export Plus Minus Le Lt.
