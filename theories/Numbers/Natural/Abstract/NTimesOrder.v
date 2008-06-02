(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export NPlusOrder.

Module NTimesOrderPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NPlusOrderPropMod := NPlusOrderPropFunct NAxiomsMod.
Open Local Scope NatScope.

Theorem mul_lt_pred :
  forall p q n m : N, S p == q -> (p * n < p * m <-> q * n + m < q * m + n).
Proof NZmul_lt_pred.

Theorem mul_lt_mono_pos_l : forall p n m : N, 0 < p -> (n < m <-> p * n < p * m).
Proof NZmul_lt_mono_pos_l.

Theorem mul_lt_mono_pos_r : forall p n m : N, 0 < p -> (n < m <-> n * p < m * p).
Proof NZmul_lt_mono_pos_r.

Theorem mul_cancel_l : forall n m p : N, p ~= 0 -> (p * n == p * m <-> n == m).
Proof NZmul_cancel_l.

Theorem mul_cancel_r : forall n m p : N, p ~= 0 -> (n * p == m * p <-> n == m).
Proof NZmul_cancel_r.

Theorem mul_id_l : forall n m : N, m ~= 0 -> (n * m == m <-> n == 1).
Proof NZmul_id_l.

Theorem mul_id_r : forall n m : N, n ~= 0 -> (n * m == n <-> m == 1).
Proof NZmul_id_r.

Theorem mul_le_mono_pos_l : forall n m p : N, 0 < p -> (n <= m <-> p * n <= p * m).
Proof NZmul_le_mono_pos_l.

Theorem mul_le_mono_pos_r : forall n m p : N, 0 < p -> (n <= m <-> n * p <= m * p).
Proof NZmul_le_mono_pos_r.

Theorem mul_pos_pos : forall n m : N, 0 < n -> 0 < m -> 0 < n * m.
Proof NZmul_pos_pos.

Theorem lt_1_mul_pos : forall n m : N, 1 < n -> 0 < m -> 1 < n * m.
Proof NZlt_1_mul_pos.

Theorem eq_mul_0 : forall n m : N, n * m == 0 <-> n == 0 \/ m == 0.
Proof NZeq_mul_0.

Theorem neq_mul_0 : forall n m : N, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof NZneq_mul_0.

Theorem eq_square_0 : forall n : N, n * n == 0 <-> n == 0.
Proof NZeq_square_0.

Theorem eq_mul_0_l : forall n m : N, n * m == 0 -> m ~= 0 -> n == 0.
Proof NZeq_mul_0_l.

Theorem eq_mul_0_r : forall n m : N, n * m == 0 -> n ~= 0 -> m == 0.
Proof NZeq_mul_0_r.

Theorem square_lt_mono : forall n m : N, n < m <-> n * n < m * m.
Proof.
intros n m; split; intro;
[apply NZsquare_lt_mono_nonneg | apply NZsquare_lt_simpl_nonneg];
try assumption; apply le_0_l.
Qed.

Theorem square_le_mono : forall n m : N, n <= m <-> n * n <= m * m.
Proof.
intros n m; split; intro;
[apply NZsquare_le_mono_nonneg | apply NZsquare_le_simpl_nonneg];
try assumption; apply le_0_l.
Qed.

Theorem mul_2_mono_l : forall n m : N, n < m -> 1 + (1 + 1) * n < (1 + 1) * m.
Proof NZmul_2_mono_l.

(* Theorems that are either not valid on Z or have different proofs on N and Z *)

Theorem mul_le_mono_l : forall n m p : N, n <= m -> p * n <= p * m.
Proof.
intros; apply NZmul_le_mono_nonneg_l. apply le_0_l. assumption.
Qed.

Theorem mul_le_mono_r : forall n m p : N, n <= m -> n * p <= m * p.
Proof.
intros; apply NZmul_le_mono_nonneg_r. apply le_0_l. assumption.
Qed.

Theorem mul_lt_mono : forall n m p q : N, n < m -> p < q -> n * p < m * q.
Proof.
intros; apply NZmul_lt_mono_nonneg; try assumption; apply le_0_l.
Qed.

Theorem mul_le_mono : forall n m p q : N, n <= m -> p <= q -> n * p <= m * q.
Proof.
intros; apply NZmul_le_mono_nonneg; try assumption; apply le_0_l.
Qed.

Theorem lt_0_mul : forall n m : N, n * m > 0 <-> n > 0 /\ m > 0.
Proof.
intros n m; split; [intro H | intros [H1 H2]].
apply -> NZlt_0_mul in H. destruct H as [[H1 H2] | [H1 H2]]. now split. false_hyp H1 nlt_0_r.
now apply NZmul_pos_pos.
Qed.

Notation mul_pos := lt_0_mul (only parsing).

Theorem eq_mul_1 : forall n m : N, n * m == 1 <-> n == 1 /\ m == 1.
Proof.
intros n m.
split; [| intros [H1 H2]; now rewrite H1, H2, mul_1_l].
intro H; destruct (NZlt_trichotomy n 1) as [H1 | [H1 | H1]].
apply -> lt_1_r in H1. rewrite H1, mul_0_l in H. false_hyp H neq_0_succ.
rewrite H1, mul_1_l in H; now split.
destruct (eq_0_gt_0_cases m) as [H2 | H2].
rewrite H2, mul_0_r in H; false_hyp H neq_0_succ.
apply -> (mul_lt_mono_pos_r m) in H1; [| assumption]. rewrite mul_1_l in H1.
assert (H3 : 1 < n * m) by now apply (lt_1_l 0 m).
rewrite H in H3; false_hyp H3 lt_irrefl.
Qed.

End NTimesOrderPropFunct.

