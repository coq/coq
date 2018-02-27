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

Require Export NAddOrder.

Module NMulOrderProp (Import N : NAxiomsMiniSig').
Include NAddOrderProp N.

(** Theorems that are either not valid on Z or have different proofs
    on N and Z *)

Theorem square_lt_mono : forall n m, n < m <-> n * n < m * m.
Proof.
intros n m; split; intro;
[apply square_lt_mono_nonneg | apply square_lt_simpl_nonneg];
try assumption; apply le_0_l.
Qed.

Theorem square_le_mono : forall n m, n <= m <-> n * n <= m * m.
Proof.
intros n m; split; intro;
[apply square_le_mono_nonneg | apply square_le_simpl_nonneg];
try assumption; apply le_0_l.
Qed.

Theorem mul_le_mono_l : forall n m p, n <= m -> p * n <= p * m.
Proof.
intros; apply mul_le_mono_nonneg_l. apply le_0_l. assumption.
Qed.

Theorem mul_le_mono_r : forall n m p, n <= m -> n * p <= m * p.
Proof.
intros; apply mul_le_mono_nonneg_r. apply le_0_l. assumption.
Qed.

Theorem mul_lt_mono : forall n m p q, n < m -> p < q -> n * p < m * q.
Proof.
intros; apply mul_lt_mono_nonneg; try assumption; apply le_0_l.
Qed.

Theorem mul_le_mono : forall n m p q, n <= m -> p <= q -> n * p <= m * q.
Proof.
intros; apply mul_le_mono_nonneg; try assumption; apply le_0_l.
Qed.

Theorem lt_0_mul' : forall n m, n * m > 0 <-> n > 0 /\ m > 0.
Proof.
intros n m; split; [intro H | intros [H1 H2]].
apply lt_0_mul in H. destruct H as [[H1 H2] | [H1 H2]]. now split.
 false_hyp H1 nlt_0_r.
now apply mul_pos_pos.
Qed.

Notation mul_pos := lt_0_mul' (only parsing).

Theorem eq_mul_1 : forall n m, n * m == 1 <-> n == 1 /\ m == 1.
Proof.
intros n m.
split; [| intros [H1 H2]; now rewrite H1, H2, mul_1_l].
intro H; destruct (lt_trichotomy n 1) as [H1 | [H1 | H1]].
apply lt_1_r in H1. rewrite H1, mul_0_l in H. order'.
rewrite H1, mul_1_l in H; now split.
destruct (eq_0_gt_0_cases m) as [H2 | H2].
rewrite H2, mul_0_r in H. order'.
apply (mul_lt_mono_pos_r m) in H1; [| assumption]. rewrite mul_1_l in H1.
assert (H3 : 1 < n * m) by now apply (lt_1_l m).
rewrite H in H3; false_hyp H3 lt_irrefl.
Qed.

(** Alternative name : *)

Definition mul_eq_1 := eq_mul_1.

End NMulOrderProp.

