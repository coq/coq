(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith_base.
Require Import BinInt.
Require Import Old_zorder.
Require Import Decidable.
Require Import Peano_dec.
Require Export Compare_dec.

Open Local Scope Z_scope.

(***************************************************************)
(** * Moving terms from one side to the other of an inequality *)

Theorem Zne_left : forall n m:Z, Zne n m -> Zne (n + - m) 0.
Proof.
  intros x y; unfold Zne in |- *; unfold not in |- *; intros H1 H2; apply H1;
    apply Zplus_reg_l with (- y); rewrite Zplus_opp_l; 
      rewrite Zplus_comm; trivial with arith.
Qed.

Theorem Zegal_left : forall n m:Z, n = m -> n + - m = 0.
Proof.
  intros x y H; apply (Zplus_reg_l y); rewrite Zplus_permute;
    rewrite Zplus_opp_r; do 2 rewrite Zplus_0_r; assumption.
Qed.

Theorem Zle_left : forall n m:Z, n <= m -> 0 <= m + - n.
Proof.
  intros x y H; replace 0 with (x + - x).
  apply Zplus_le_compat_r; trivial.
  apply Zplus_opp_r.
Qed.

Theorem Zle_left_rev : forall n m:Z, 0 <= m + - n -> n <= m.
Proof.
  intros x y H; apply Zplus_le_reg_r with (- x).
  rewrite Zplus_opp_r; trivial.
Qed.

Theorem Zlt_left_rev : forall n m:Z, 0 < m + - n -> n < m.
Proof.
  intros x y H; apply Zplus_lt_reg_r with (- x).
  rewrite Zplus_opp_r; trivial.
Qed.

Theorem Zlt_left : forall n m:Z, n < m -> 0 <= m + -1 + - n.
Proof.
  intros x y H; apply Zle_left; apply Zsucc_le_reg;
    change (Zsucc x <= Zsucc (Zpred y)) in |- *; rewrite <- Zsucc_pred;
      apply Zlt_le_succ; assumption.
Qed.

Theorem Zlt_left_lt : forall n m:Z, n < m -> 0 < m + - n.
Proof.
  intros x y H; replace 0 with (x + - x).
  apply Zplus_lt_compat_r; trivial.
  apply Zplus_opp_r.
Qed.

Theorem Zge_left : forall n m:Z, n >= m -> 0 <= n + - m.
Proof.
  intros x y H; apply Zle_left; apply Zge_le; assumption.
Qed.

Theorem Zgt_left : forall n m:Z, n > m -> 0 <= n + -1 + - m.
Proof.
  intros x y H; apply Zlt_left; apply Zgt_lt; assumption.
Qed.

Theorem Zgt_left_gt : forall n m:Z, n > m -> n + - m > 0.
Proof.
  intros x y H; replace 0 with (y + - y).
  apply Zplus_gt_compat_r; trivial.
  apply Zplus_opp_r.
Qed.

Theorem Zgt_left_rev : forall n m:Z, n + - m > 0 -> n > m.
Proof.
  intros x y H; apply Zplus_gt_reg_r with (- y).
  rewrite Zplus_opp_r; trivial.
Qed.

(**********************************************************************)
(** * Factorization lemmas *)

Theorem Zred_factor0 : forall n:Z, n = n * 1.
  intro x; rewrite (Zmult_1_r x); reflexivity.
Qed.

Theorem Zred_factor1 : forall n:Z, n + n = n * 2.
Proof.
  exact Zplus_diag_eq_mult_2.
Qed.

Theorem Zred_factor2 : forall n m:Z, n + n * m = n * (1 + m).
Proof.
  intros x y; pattern x at 1 in |- *; rewrite <- (Zmult_1_r x);
    rewrite <- Zmult_plus_distr_r; trivial with arith.
Qed.

Theorem Zred_factor3 : forall n m:Z, n * m + n = n * (1 + m).
Proof.
  intros x y; pattern x at 2 in |- *; rewrite <- (Zmult_1_r x);
    rewrite <- Zmult_plus_distr_r; rewrite Zplus_comm; 
      trivial with arith.
Qed.

Theorem Zred_factor4 : forall n m p:Z, n * m + n * p = n * (m + p).
Proof.
  intros x y z; symmetry  in |- *; apply Zmult_plus_distr_r.
Qed.

Theorem Zred_factor5 : forall n m:Z, n * 0 + m = m.
Proof.
  intros x y; rewrite <- Zmult_0_r_reverse; auto with arith.
Qed.

Theorem Zred_factor6 : forall n:Z, n = n + 0.
Proof.
  intro; rewrite Zplus_0_r; trivial with arith.
Qed.

Theorem Zle_mult_approx :
  forall n m p:Z, n > 0 -> p > 0 -> 0 <= m -> 0 <= m * n + p.
Proof.
  intros x y z H1 H2 H3; apply Zle_trans with (m := y * x);
    [ apply Zmult_gt_0_le_0_compat; assumption
      | pattern (y * x) at 1 in |- *; rewrite <- Zplus_0_r;
	apply Zplus_le_compat_l; apply Zlt_le_weak; apply Zgt_lt; 
	  assumption ].
Qed.

Theorem Zmult_le_approx :
  forall n m p:Z, n > 0 -> n > p -> 0 <= m * n + p -> 0 <= m.
Proof.
  intros x y z H1 H2 H3; apply Zlt_succ_le; apply Zmult_gt_0_lt_0_reg_r with x;
    [ assumption
      | apply Zle_lt_trans with (1 := H3); rewrite <- Zmult_succ_l_reverse;
	apply Zplus_lt_compat_l; apply Zgt_lt; assumption ].
Qed.

