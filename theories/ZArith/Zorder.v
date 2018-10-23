(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Binary Integers : results about order predicates *)
(** Initial author : Pierre Crégut (CNET, Lannion, France) *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

Require Import BinPos BinInt Decidable Zcompare.
Require Import Arith_base. (* Useless now, for compatibility only *)

Local Open Scope Z_scope.

(*********************************************************)
(** Properties of the order relations on binary integers *)

(** * Trichotomy *)

Theorem Ztrichotomy_inf n m : {n < m} + {n = m} + {n > m}.
Proof.
  unfold ">", "<". generalize (Z.compare_eq n m).
  destruct (n ?= m); [ left; right | left; left | right]; auto.
Defined.

Theorem Ztrichotomy n m : n < m \/ n = m \/ n > m.
Proof.
  Z.swap_greater. apply Z.lt_trichotomy.
Qed.

(**********************************************************************)
(** * Decidability of equality and order on Z *)

Notation dec_eq := Z.eq_decidable (only parsing).
Notation dec_Zle := Z.le_decidable (only parsing).
Notation dec_Zlt := Z.lt_decidable (only parsing).

Theorem dec_Zne n m : decidable (Zne n m).
Proof.
  destruct (Z.eq_decidable n m); [right|left]; subst; auto.
Qed.

Theorem dec_Zgt n m : decidable (n > m).
Proof.
  destruct (Z.lt_decidable m n); [left|right]; Z.swap_greater; auto.
Qed.

Theorem dec_Zge n m : decidable (n >= m).
Proof.
  destruct (Z.le_decidable m n); [left|right]; Z.swap_greater; auto.
Qed.

Theorem not_Zeq n m : n <> m -> n < m \/ m < n.
Proof.
  apply Z.lt_gt_cases.
Qed.

(** * Relating strict and large orders *)

Notation Zgt_lt := Z.gt_lt (compat "8.7").
Notation Zlt_gt := Z.lt_gt (compat "8.7").
Notation Zge_le := Z.ge_le (compat "8.7").
Notation Zle_ge := Z.le_ge (compat "8.7").
Notation Zgt_iff_lt := Z.gt_lt_iff (only parsing).
Notation Zge_iff_le := Z.ge_le_iff (only parsing).

Lemma Zle_not_lt n m : n <= m -> ~ m < n.
Proof.
 apply Z.le_ngt.
Qed.

Lemma Zlt_not_le n m : n < m -> ~ m <= n.
Proof.
 apply Z.lt_nge.
Qed.

Lemma Zle_not_gt n m : n <= m -> ~ n > m.
Proof.
  trivial.
Qed.

Lemma Zgt_not_le n m : n > m -> ~ n <= m.
Proof.
  Z.swap_greater. apply Z.lt_nge.
Qed.

Lemma Znot_ge_lt n m : ~ n >= m -> n < m.
Proof.
  Z.swap_greater. apply Z.nle_gt.
Qed.

Lemma Znot_lt_ge n m : ~ n < m -> n >= m.
Proof.
  trivial.
Qed.

Lemma Znot_gt_le n m: ~ n > m -> n <= m.
Proof.
  trivial.
Qed.

Lemma Znot_le_gt n m : ~ n <= m -> n > m.
Proof.
  Z.swap_greater. apply Z.nle_gt.
Qed.

Lemma not_Zne n m : ~ Zne n m -> n = m.
Proof.
  intros H.
  destruct (Z.eq_decidable n m); [assumption|now elim H].
Qed.

(** * Equivalence and order properties *)

(** Reflexivity *)

Notation Zle_refl := Z.le_refl (compat "8.7").
Notation Zeq_le := Z.eq_le_incl (only parsing).

Hint Resolve Z.le_refl: zarith.

(** Antisymmetry *)

Notation Zle_antisym := Z.le_antisymm (only parsing).

(** Asymmetry *)

Notation Zlt_asym := Z.lt_asymm (only parsing).

Lemma Zgt_asym n m : n > m -> ~ m > n.
Proof.
  Z.swap_greater. apply Z.lt_asymm.
Qed.

(** Irreflexivity *)

Notation Zlt_irrefl := Z.lt_irrefl (compat "8.7").
Notation Zlt_not_eq := Z.lt_neq (only parsing).

Lemma Zgt_irrefl n : ~ n > n.
Proof.
  Z.swap_greater. apply Z.lt_irrefl.
Qed.

(** Large = strict or equal *)

Notation Zlt_le_weak := Z.lt_le_incl (only parsing).
Notation Zle_lt_or_eq_iff := Z.lt_eq_cases (only parsing).

Lemma Zle_lt_or_eq n m : n <= m -> n < m \/ n = m.
Proof.
  apply Z.lt_eq_cases.
Qed.

(** Dichotomy *)

Notation Zle_or_lt := Z.le_gt_cases (only parsing).

(** Transitivity of strict orders *)

Notation Zlt_trans := Z.lt_trans (compat "8.7").

Lemma Zgt_trans n m p : n > m -> m > p -> n > p.
Proof.
  Z.swap_greater. intros; now transitivity m.
Qed.

(** Mixed transitivity *)

Notation Zlt_le_trans := Z.lt_le_trans (compat "8.7").
Notation Zle_lt_trans := Z.le_lt_trans (compat "8.7").

Lemma Zle_gt_trans n m p : m <= n -> m > p -> n > p.
Proof.
  Z.swap_greater. Z.order.
Qed.

Lemma Zgt_le_trans n m p : n > m -> p <= m -> n > p.
Proof.
  Z.swap_greater. Z.order.
Qed.

(** Transitivity of large orders *)

Notation Zle_trans := Z.le_trans (compat "8.7").

Lemma Zge_trans n m p : n >= m -> m >= p -> n >= p.
Proof.
  Z.swap_greater. Z.order.
Qed.

Hint Resolve Z.le_trans: zarith.

(** * Compatibility of order and operations on Z *)

(** ** Successor *)

(** Compatibility of successor wrt to order *)

Lemma Zsucc_le_compat n m : m <= n -> Z.succ m <= Z.succ n.
Proof.
  apply Z.succ_le_mono.
Qed.

Lemma Zsucc_lt_compat n m : n < m -> Z.succ n < Z.succ m.
Proof.
  apply Z.succ_lt_mono.
Qed.

Lemma Zsucc_gt_compat n m : m > n -> Z.succ m > Z.succ n.
Proof.
  Z.swap_greater. apply Z.succ_lt_mono.
Qed.

Hint Resolve Zsucc_le_compat: zarith.

(** Simplification of successor wrt to order *)

Lemma Zsucc_gt_reg n m : Z.succ m > Z.succ n -> m > n.
Proof.
  Z.swap_greater. apply Z.succ_lt_mono.
Qed.

Lemma Zsucc_le_reg n m : Z.succ m <= Z.succ n -> m <= n.
Proof.
  apply Z.succ_le_mono.
Qed.

Lemma Zsucc_lt_reg n m : Z.succ n < Z.succ m -> n < m.
Proof.
  apply Z.succ_lt_mono.
Qed.

(** Special base instances of order *)

Notation Zlt_succ := Z.lt_succ_diag_r (only parsing).
Notation Zlt_pred := Z.lt_pred_l (only parsing).

Lemma Zgt_succ n : Z.succ n > n.
Proof.
  Z.swap_greater. apply Z.lt_succ_diag_r.
Qed.

Lemma Znot_le_succ n : ~ Z.succ n <= n.
Proof.
  apply Z.lt_nge, Z.lt_succ_diag_r.
Qed.

(** Relating strict and large order using successor or predecessor *)

Notation Zlt_succ_r := Z.lt_succ_r (compat "8.7").
Notation Zle_succ_l := Z.le_succ_l (compat "8.7").

Lemma Zgt_le_succ n m : m > n -> Z.succ n <= m.
Proof.
  Z.swap_greater. apply Z.le_succ_l.
Qed.

Lemma Zle_gt_succ n m : n <= m -> Z.succ m > n.
Proof.
  Z.swap_greater. apply Z.lt_succ_r.
Qed.

Lemma Zle_lt_succ n m : n <= m -> n < Z.succ m.
Proof.
  apply Z.lt_succ_r.
Qed.

Lemma Zlt_le_succ n m : n < m -> Z.succ n <= m.
Proof.
  apply Z.le_succ_l.
Qed.

Lemma Zgt_succ_le n m : Z.succ m > n -> n <= m.
Proof.
  Z.swap_greater. apply Z.lt_succ_r.
Qed.

Lemma Zlt_succ_le n m : n < Z.succ m -> n <= m.
Proof.
  apply Z.lt_succ_r.
Qed.

Lemma Zle_succ_gt n m : Z.succ n <= m -> m > n.
Proof.
  Z.swap_greater. apply Z.le_succ_l.
Qed.

(** Weakening order *)

Notation Zle_succ := Z.le_succ_diag_r (only parsing).
Notation Zle_pred := Z.le_pred_l (only parsing).
Notation Zlt_lt_succ := Z.lt_lt_succ_r (only parsing).
Notation Zle_le_succ := Z.le_le_succ_r (only parsing).

Lemma Zle_succ_le n m : Z.succ n <= m -> n <= m.
Proof.
  intros. now apply Z.lt_le_incl, Z.le_succ_l.
Qed.

Hint Resolve Z.le_succ_diag_r: zarith.
Hint Resolve Z.le_le_succ_r: zarith.

(** Relating order wrt successor and order wrt predecessor *)

Lemma Zgt_succ_pred n m : m > Z.succ n -> Z.pred m > n.
Proof.
  Z.swap_greater. apply Z.lt_succ_lt_pred.
Qed.

Lemma Zlt_succ_pred n m : Z.succ n < m -> n < Z.pred m.
Proof.
  apply Z.lt_succ_lt_pred.
Qed.

(** Relating strict order and large order on positive *)

Lemma Zlt_0_le_0_pred n : 0 < n -> 0 <= Z.pred n.
Proof.
  apply Z.lt_le_pred.
Qed.

Lemma Zgt_0_le_0_pred n : n > 0 -> 0 <= Z.pred n.
Proof.
  Z.swap_greater. apply Z.lt_le_pred.
Qed.

(** Special cases of ordered integers *)

Notation Zlt_0_1 := Z.lt_0_1 (compat "8.7").
Notation Zle_0_1 := Z.le_0_1 (compat "8.7").

Lemma Zle_neg_pos : forall p q:positive, Zneg p <= Zpos q.
Proof.
  exact Pos2Z.neg_le_pos.
Qed.

Lemma Zgt_pos_0 : forall p:positive, Zpos p > 0.
Proof.
  easy.
Qed.

(* weaker but useful (in [Z.pow] for instance) *)
Lemma Zle_0_pos : forall p:positive, 0 <= Zpos p.
Proof.
  exact Pos2Z.pos_is_nonneg.
Qed.

Lemma Zlt_neg_0 : forall p:positive, Zneg p < 0.
Proof.
  exact Pos2Z.neg_is_neg.
Qed.

Lemma Zle_0_nat : forall n:nat, 0 <= Z.of_nat n.
Proof.
  induction n; simpl; intros. apply Z.le_refl. easy.
Qed.

Hint Immediate Z.eq_le_incl: zarith.

(** Derived lemma *)

Lemma Zgt_succ_gt_or_eq n m : Z.succ n > m -> n > m \/ m = n.
Proof.
  Z.swap_greater. intros. now apply Z.lt_eq_cases, Z.lt_succ_r.
Qed.

(** ** Addition *)
(** Compatibility of addition wrt to order *)

Notation Zplus_lt_le_compat := Z.add_lt_le_mono (only parsing).
Notation Zplus_le_lt_compat := Z.add_le_lt_mono (only parsing).
Notation Zplus_le_compat := Z.add_le_mono (only parsing).
Notation Zplus_lt_compat := Z.add_lt_mono (only parsing).

Lemma Zplus_gt_compat_l n m p : n > m -> p + n > p + m.
Proof.
  Z.swap_greater. apply Z.add_lt_mono_l.
Qed.

Lemma Zplus_gt_compat_r n m p : n > m -> n + p > m + p.
Proof.
  Z.swap_greater. apply Z.add_lt_mono_r.
Qed.

Lemma Zplus_le_compat_l n m p : n <= m -> p + n <= p + m.
Proof.
  apply Z.add_le_mono_l.
Qed.

Lemma Zplus_le_compat_r n m p : n <= m -> n + p <= m + p.
Proof.
  apply Z.add_le_mono_r.
Qed.

Lemma Zplus_lt_compat_l n m p : n < m -> p + n < p + m.
Proof.
  apply Z.add_lt_mono_l.
Qed.

Lemma Zplus_lt_compat_r n m p : n < m -> n + p < m + p.
Proof.
  apply Z.add_lt_mono_r.
Qed.

(** Compatibility of addition wrt to being positive *)

Notation Zplus_le_0_compat := Z.add_nonneg_nonneg (only parsing).

(** Simplification of addition wrt to order *)

Lemma Zplus_le_reg_l n m p : p + n <= p + m -> n <= m.
Proof.
 apply Z.add_le_mono_l.
Qed.

Lemma Zplus_le_reg_r n m p : n + p <= m + p -> n <= m.
Proof.
 apply Z.add_le_mono_r.
Qed.

Lemma Zplus_lt_reg_l n m p : p + n < p + m -> n < m.
Proof.
 apply Z.add_lt_mono_l.
Qed.

Lemma Zplus_lt_reg_r n m p : n + p < m + p -> n < m.
Proof.
 apply Z.add_lt_mono_r.
Qed.

Lemma Zplus_gt_reg_l n m p : p + n > p + m -> n > m.
Proof.
 Z.swap_greater. apply Z.add_lt_mono_l.
Qed.

Lemma Zplus_gt_reg_r n m p : n + p > m + p -> n > m.
Proof.
 Z.swap_greater. apply Z.add_lt_mono_r.
Qed.

(** ** Multiplication *)
(** Compatibility of multiplication by a positive wrt to order *)

Lemma Zmult_le_compat_r n m p : n <= m -> 0 <= p -> n * p <= m * p.
Proof.
 intros. now apply Z.mul_le_mono_nonneg_r.
Qed.

Lemma Zmult_le_compat_l n m p : n <= m -> 0 <= p -> p * n <= p * m.
Proof.
 intros. now apply Z.mul_le_mono_nonneg_l.
Qed.

Lemma Zmult_lt_compat_r n m p : 0 < p -> n < m -> n * p < m * p.
Proof.
 apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_compat_r n m p : p > 0 -> n > m -> n * p > m * p.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_0_lt_compat_r n m p : p > 0 -> n < m -> n * p < m * p.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_0_le_compat_r n m p : p > 0 -> n <= m -> n * p <= m * p.
Proof.
 Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_lt_0_le_compat_r n m p : 0 < p -> n <= m -> n * p <= m * p.
Proof.
 apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_gt_0_lt_compat_l n m p : p > 0 -> n < m -> p * n < p * m.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_lt_compat_l n m p : 0 < p -> n < m -> p * n < p * m.
Proof.
 apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_gt_compat_l n m p : p > 0 -> n > m -> p * n > p * m.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_ge_compat_r n m p : n >= m -> p >= 0 -> n * p >= m * p.
Proof.
 Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg_r.
Qed.

Lemma Zmult_ge_compat_l n m p : n >= m -> p >= 0 -> p * n >= p * m.
Proof.
 Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg_l.
Qed.

Lemma Zmult_ge_compat n m p q :
  n >= p -> m >= q -> p >= 0 -> q >= 0 -> n * m >= p * q.
Proof.
 Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg.
Qed.

Lemma Zmult_le_compat n m p q :
  n <= p -> m <= q -> 0 <= n -> 0 <= m -> n * m <= p * q.
Proof.
 intros. now apply Z.mul_le_mono_nonneg.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zmult_gt_0_lt_reg_r n m p : p > 0 -> n * p < m * p -> n < m.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_lt_reg_r n m p : 0 < p -> n * p < m * p -> n < m.
Proof.
 apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_le_reg_r n m p : p > 0 -> n * p <= m * p -> n <= m.
Proof.
 Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_lt_0_le_reg_r n m p : 0 < p -> n * p <= m * p -> n <= m.
Proof.
 apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_ge_reg_r n m p : p > 0 -> n * p >= m * p -> n >= m.
Proof.
 Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_gt_reg_r n m p : p > 0 -> n * p > m * p -> n > m.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_lt_compat n m p q :
  0 <= n < p -> 0 <= m < q -> n * m < p * q.
Proof.
 intros (Hn,Hnp) (Hm,Hmq). now apply Z.mul_lt_mono_nonneg.
Qed.

Lemma Zmult_lt_compat2 n m p q :
  0 < n <= p -> 0 < m < q -> n * m < p * q.
Proof.
  intros (Hn, Hnp) (Hm,Hmq).
  apply Z.le_lt_trans with (p * m).
   apply Z.mul_le_mono_pos_r; trivial.
   apply Z.mul_lt_mono_pos_l; Z.order.
Qed.

(** Compatibility of multiplication by a positive wrt to being positive *)

Notation Zmult_le_0_compat := Z.mul_nonneg_nonneg (only parsing).
Notation Zmult_lt_0_compat := Z.mul_pos_pos (only parsing).
Notation Zmult_lt_O_compat := Z.mul_pos_pos (only parsing).

Lemma Zmult_gt_0_compat n m : n > 0 -> m > 0 -> n * m > 0.
Proof.
 Z.swap_greater. apply Z.mul_pos_pos.
Qed.

(* To remove someday ... *)

Lemma Zmult_gt_0_le_0_compat n m : n > 0 -> 0 <= m -> 0 <= m * n.
Proof.
 Z.swap_greater. intros. apply Z.mul_nonneg_nonneg. trivial.
  now apply Z.lt_le_incl.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zmult_le_0_reg_r n m : n > 0 -> 0 <= m * n -> 0 <= m.
Proof.
 Z.swap_greater. apply Z.mul_nonneg_cancel_r.
Qed.

Lemma Zmult_lt_0_reg_r n m : 0 < n -> 0 < m * n -> 0 < m.
Proof.
 apply Z.mul_pos_cancel_r.
Qed.

Lemma Zmult_gt_0_lt_0_reg_r n m : n > 0 -> 0 < m * n -> 0 < m.
Proof.
 Z.swap_greater. apply Z.mul_pos_cancel_r.
Qed.

Lemma Zmult_gt_0_reg_l n m : n > 0 -> n * m > 0 -> m > 0.
Proof.
 Z.swap_greater. apply Z.mul_pos_cancel_l.
Qed.

(** ** Square *)
(** Simplification of square wrt order *)

Lemma Zlt_square_simpl n m : 0 <= n -> m * m < n * n -> m < n.
Proof.
 apply Z.square_lt_simpl_nonneg.
Qed.

Lemma Zgt_square_simpl n m : n >= 0 -> n * n > m * m -> n > m.
Proof.
 Z.swap_greater. apply Z.square_lt_simpl_nonneg.
Qed.

(** * Equivalence between inequalities *)

Notation Zle_plus_swap := Z.le_add_le_sub_r (only parsing).
Notation Zlt_plus_swap := Z.lt_add_lt_sub_r (only parsing).
Notation Zlt_minus_simpl_swap := Z.lt_sub_pos (only parsing).

Lemma Zeq_plus_swap n m p : n + p = m <-> n = m - p.
Proof.
 apply Z.add_move_r.
Qed.

Lemma Zlt_0_minus_lt n m : 0 < n - m -> m < n.
Proof.
 apply Z.lt_0_sub.
Qed.

Lemma Zle_0_minus_le n m : 0 <= n - m -> m <= n.
Proof.
 apply Z.le_0_sub.
Qed.

Lemma Zle_minus_le_0 n m : m <= n -> 0 <= n - m.
Proof.
 apply Z.le_0_sub.
Qed.

(** For compatibility *)
Notation Zlt_O_minus_lt := Zlt_0_minus_lt (only parsing).
