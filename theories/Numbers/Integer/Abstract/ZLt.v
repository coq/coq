(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export ZMul.

Module ZOrderProp (Import Z : ZAxiomsMiniSig').
Include ZMulProp Z.

(** Instances of earlier theorems for m == 0 *)

Theorem neg_pos_cases : forall n, n ~= 0 <-> n < 0 \/ n > 0.
Proof.
intro; apply lt_gt_cases.
Qed.

Theorem nonpos_pos_cases : forall n, n <= 0 \/ n > 0.
Proof.
intro; apply le_gt_cases.
Qed.

Theorem neg_nonneg_cases : forall n, n < 0 \/ n >= 0.
Proof.
intro; apply lt_ge_cases.
Qed.

Theorem nonpos_nonneg_cases : forall n, n <= 0 \/ n >= 0.
Proof.
intro; apply le_ge_cases.
Qed.

Ltac zinduct n := induction_maker n ltac:(apply order_induction_0).

(** Theorems that are either not valid on N or have different proofs
    on N and Z *)

Theorem lt_pred_l : forall n, P n < n.
Proof.
intro n; rewrite <- (succ_pred n) at 2; apply lt_succ_diag_r.
Qed.

Theorem le_pred_l : forall n, P n <= n.
Proof.
intro; apply lt_le_incl; apply lt_pred_l.
Qed.

Theorem lt_le_pred : forall n m, n < m <-> n <= P m.
Proof.
intros n m; rewrite <- (succ_pred m); rewrite pred_succ. apply lt_succ_r.
Qed.

Theorem nle_pred_r : forall n, ~ n <= P n.
Proof.
intro; rewrite <- lt_le_pred; apply lt_irrefl.
Qed.

Theorem lt_pred_le : forall n m, P n < m <-> n <= m.
Proof.
intros n m; rewrite <- (succ_pred n) at 2.
symmetry; apply le_succ_l.
Qed.

Theorem lt_lt_pred : forall n m, n < m -> P n < m.
Proof.
intros; apply lt_pred_le; now apply lt_le_incl.
Qed.

Theorem le_le_pred : forall n m, n <= m -> P n <= m.
Proof.
intros; apply lt_le_incl; now apply lt_pred_le.
Qed.

Theorem lt_pred_lt : forall n m, n < P m -> n < m.
Proof.
intros n m H; apply lt_trans with (P m); [assumption | apply lt_pred_l].
Qed.

Theorem le_pred_lt : forall n m, n <= P m -> n <= m.
Proof.
intros; apply lt_le_incl; now apply lt_le_pred.
Qed.

Theorem pred_lt_mono : forall n m, n < m <-> P n < P m.
Proof.
intros; rewrite lt_le_pred; symmetry; apply lt_pred_le.
Qed.

Theorem pred_le_mono : forall n m, n <= m <-> P n <= P m.
Proof.
intros; rewrite <- lt_pred_le; now rewrite lt_le_pred.
Qed.

Theorem lt_succ_lt_pred : forall n m, S n < m <-> n < P m.
Proof.
intros n m; now rewrite (pred_lt_mono (S n) m), pred_succ.
Qed.

Theorem le_succ_le_pred : forall n m, S n <= m <-> n <= P m.
Proof.
intros n m; now rewrite (pred_le_mono (S n) m), pred_succ.
Qed.

Theorem lt_pred_lt_succ : forall n m, P n < m <-> n < S m.
Proof.
intros; rewrite lt_pred_le; symmetry; apply lt_succ_r.
Qed.

Theorem le_pred_lt_succ : forall n m, P n <= m <-> n <= S m.
Proof.
intros n m; now rewrite (pred_le_mono n (S m)), pred_succ.
Qed.

Theorem neq_pred_l : forall n, P n ~= n.
Proof.
intro; apply lt_neq; apply lt_pred_l.
Qed.

Theorem lt_m1_r : forall n m, n < m -> m < 0 -> n < -1.
Proof.
intros n m H1 H2. apply lt_le_pred in H2.
setoid_replace (P 0) with (-1) in H2. now apply lt_le_trans with m.
apply eq_opp_r. now rewrite one_succ, opp_pred, opp_0.
Qed.

End ZOrderProp.

