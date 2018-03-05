(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Theorems about [gt] in [nat].

 This file is DEPRECATED now, see module [PeanoNat.Nat] instead,
 which favor [lt] over [gt].

 [gt] is defined in [Init/Peano.v] as:
<<
Definition gt (n m:nat) := m < n.
>>
*)

Require Import PeanoNat Le Lt Plus.
Local Open Scope nat_scope.

(** * Order and successor *)

Theorem gt_Sn_O n : S n > 0.
Proof Nat.lt_0_succ _.

Theorem gt_Sn_n n : S n > n.
Proof Nat.lt_succ_diag_r _.

Theorem gt_n_S n m : n > m -> S n > S m.
Proof.
 apply Nat.succ_lt_mono.
Qed.

Lemma gt_S_n n m : S m > S n -> m > n.
Proof.
 apply Nat.succ_lt_mono.
Qed.

Theorem gt_S n m : S n > m -> n > m \/ m = n.
Proof.
 intro. now apply Nat.lt_eq_cases, Nat.succ_le_mono.
Qed.

Lemma gt_pred n m : m > S n -> pred m > n.
Proof.
 apply Nat.lt_succ_lt_pred.
Qed.

(** * Irreflexivity *)

Lemma gt_irrefl n : ~ n > n.
Proof Nat.lt_irrefl _.

(** * Asymmetry *)

Lemma gt_asym n m : n > m -> ~ m > n.
Proof Nat.lt_asymm _ _.

(** * Relating strict and large orders *)

Lemma le_not_gt n m : n <= m -> ~ n > m.
Proof.
 apply Nat.le_ngt.
Qed.

Lemma gt_not_le n m : n > m -> ~ n <= m.
Proof.
 apply Nat.lt_nge.
Qed.

Theorem le_S_gt n m : S n <= m -> m > n.
Proof.
 apply Nat.le_succ_l.
Qed.

Lemma gt_S_le n m : S m > n -> n <= m.
Proof.
 apply Nat.succ_le_mono.
Qed.

Lemma gt_le_S n m : m > n -> S n <= m.
Proof.
 apply Nat.le_succ_l.
Qed.

Lemma le_gt_S n m : n <= m -> S m > n.
Proof.
 apply Nat.succ_le_mono.
Qed.

(** * Transitivity *)

Theorem le_gt_trans n m p : m <= n -> m > p -> n > p.
Proof.
 intros. now apply Nat.lt_le_trans with m.
Qed.

Theorem gt_le_trans n m p : n > m -> p <= m -> n > p.
Proof.
 intros. now apply Nat.le_lt_trans with m.
Qed.

Lemma gt_trans n m p : n > m -> m > p -> n > p.
Proof.
 intros. now apply Nat.lt_trans with m.
Qed.

Theorem gt_trans_S n m p : S n > m -> m > p -> n > p.
Proof.
 intros. apply Nat.lt_le_trans with m; trivial. now apply Nat.succ_le_mono.
Qed.

(** * Comparison to 0 *)

Theorem gt_0_eq n : n > 0 \/ 0 = n.
Proof.
 destruct n; [now right | left; apply Nat.lt_0_succ].
Qed.

(** * Simplification and compatibility *)

Lemma plus_gt_reg_l n m p : p + n > p + m -> n > m.
Proof.
 apply Nat.add_lt_mono_l.
Qed.

Lemma plus_gt_compat_l n m p : n > m -> p + n > p + m.
Proof.
 apply Nat.add_lt_mono_l.
Qed.

(** * Hints *)

Hint Resolve gt_Sn_O gt_Sn_n gt_n_S : arith.
Hint Immediate gt_S_n gt_pred : arith.
Hint Resolve gt_irrefl gt_asym : arith.
Hint Resolve le_not_gt gt_not_le : arith.
Hint Immediate le_S_gt gt_S_le : arith.
Hint Resolve gt_le_S le_gt_S : arith.
Hint Resolve gt_trans_S le_gt_trans gt_le_trans: arith.
Hint Resolve plus_gt_compat_l: arith.

(* begin hide *)
Notation gt_O_eq := gt_0_eq (only parsing).
(* end hide *)
