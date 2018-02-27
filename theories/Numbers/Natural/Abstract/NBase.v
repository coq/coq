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

Require Export Decidable.
Require Export NAxioms.
Require Import NZProperties.

Module NBaseProp (Import N : NAxiomsMiniSig').
(** First, we import all known facts about both natural numbers and integers. *)
Include NZProp N.

(** From [pred_0] and order facts, we can prove that 0 isn't a successor. *)

Theorem neq_succ_0 : forall n, S n ~= 0.
Proof.
 intros n EQ.
 assert (EQ' := pred_succ n).
 rewrite EQ, pred_0 in EQ'.
 rewrite <- EQ' in EQ.
 now apply (neq_succ_diag_l 0).
Qed.

Theorem neq_0_succ : forall n, 0 ~= S n.
Proof.
intro n; apply neq_sym; apply neq_succ_0.
Qed.

(** Next, we show that all numbers are nonnegative and recover regular
    induction from the bidirectional induction on NZ *)

Theorem le_0_l : forall n, 0 <= n.
Proof.
nzinduct n.
now apply eq_le_incl.
intro n; split.
apply le_le_succ_r.
intro H; apply le_succ_r in H; destruct H as [H | H].
assumption.
symmetry in H; false_hyp H neq_succ_0.
Qed.

Theorem induction :
  forall A : N.t -> Prop, Proper (N.eq==>iff) A ->
    A 0 -> (forall n, A n -> A (S n)) -> forall n, A n.
Proof.
intros A A_wd A0 AS n; apply right_induction with 0; try assumption.
intros; auto; apply le_0_l. apply le_0_l.
Qed.

(** The theorems [bi_induction], [central_induction] and the tactic [nzinduct]
refer to bidirectional induction, which is not useful on natural
numbers. Therefore, we define a new induction tactic for natural numbers.
We do not have to call "Declare Left Step" and "Declare Right Step"
commands again, since the data for stepl and stepr tactics is inherited
from NZ. *)

Ltac induct n := induction_maker n ltac:(apply induction).

Theorem case_analysis :
  forall A : N.t -> Prop, Proper (N.eq==>iff) A ->
    A 0 -> (forall n, A (S n)) -> forall n, A n.
Proof.
intros; apply induction; auto.
Qed.

Ltac cases n := induction_maker n ltac:(apply case_analysis).

Theorem neq_0 : ~ forall n, n == 0.
Proof.
intro H; apply (neq_succ_0 0). apply H.
Qed.

Theorem neq_0_r : forall n, n ~= 0 <-> exists m, n == S m.
Proof.
cases n. split; intro H;
[now elim H | destruct H as [m H]; symmetry in H; false_hyp H neq_succ_0].
intro n; split; intro H; [now exists n | apply neq_succ_0].
Qed.

Theorem zero_or_succ : forall n, n == 0 \/ exists m, n == S m.
Proof.
cases n.
now left.
intro n; right; now exists n.
Qed.

Theorem eq_pred_0 : forall n, P n == 0 <-> n == 0 \/ n == 1.
Proof.
cases n.
rewrite pred_0. now split; [left|].
intro n. rewrite pred_succ.
split. intros H; right. now rewrite H, one_succ.
intros [H|H]. elim (neq_succ_0 _ H).
apply succ_inj_wd. now rewrite <- one_succ.
Qed.

Theorem succ_pred : forall n, n ~= 0 -> S (P n) == n.
Proof.
cases n.
intro H; exfalso; now apply H.
intros; now rewrite pred_succ.
Qed.

Theorem pred_inj : forall n m, n ~= 0 -> m ~= 0 -> P n == P m -> n == m.
Proof.
intros n m; cases n.
intros H; exfalso; now apply H.
intros n _; cases m.
intros H; exfalso; now apply H.
intros m H2 H3. do 2 rewrite pred_succ in H3. now rewrite H3.
Qed.

(** The following induction principle is useful for reasoning about, e.g.,
Fibonacci numbers *)

Section PairInduction.

Variable A : N.t -> Prop.
Hypothesis A_wd : Proper (N.eq==>iff) A.

Theorem pair_induction :
  A 0 -> A 1 ->
    (forall n, A n -> A (S n) -> A (S (S n))) -> forall n, A n.
Proof.
rewrite one_succ.
intros until 3.
assert (D : forall n, A n /\ A (S n)); [ |intro n; exact (proj1 (D n))].
induct n; [ | intros n [IH1 IH2]]; auto.
Qed.

End PairInduction.

(** The following is useful for reasoning about, e.g., Ackermann function *)

Section TwoDimensionalInduction.

Variable R : N.t -> N.t -> Prop.
Hypothesis R_wd : Proper (N.eq==>N.eq==>iff) R.

Theorem two_dim_induction :
   R 0 0 ->
   (forall n m, R n m -> R n (S m)) ->
   (forall n, (forall m, R n m) -> R (S n) 0) -> forall n m, R n m.
Proof.
intros H1 H2 H3. induct n.
induct m.
exact H1. exact (H2 0).
intros n IH. induct m.
now apply H3. exact (H2 (S n)).
Qed.

End TwoDimensionalInduction.


Section DoubleInduction.

Variable R : N.t -> N.t -> Prop.
Hypothesis R_wd : Proper (N.eq==>N.eq==>iff) R.

Theorem double_induction :
   (forall m, R 0 m) ->
   (forall n, R (S n) 0) ->
   (forall n m, R n m -> R (S n) (S m)) -> forall n m, R n m.
Proof.
intros H1 H2 H3; induct n; auto.
intros n H; cases m; auto.
Qed.

End DoubleInduction.

Ltac double_induct n m :=
  try intros until n;
  try intros until m;
  pattern n, m; apply double_induction; clear n m;
  [solve_proper | | | ].

End NBaseProp.

