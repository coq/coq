(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export Decidable.
Require Export NAxioms.
Require Import NZMulOrder.

Module NBaseProp (Import N : NAxiomsMiniSig').
  (** First, we import all known facts about modules implementing [NZAxiomsSig]. *)
Include NZMulOrderProp N.

(** Now we prove that [NAxiomsMiniSig'] specializes [NZAxioms.IsNatInt]. *)

Lemma Private_succ_pred n : n ~= 0 -> S (P n) == n.
Proof.
  intros Hn; apply (lt_succ_pred 0), le_neq; split; [| exact (neq_sym _ _ Hn)].
  destruct (le_gt_cases 0 n) as [I | I%lt_succ_pred]; [exact I | exfalso].
  rewrite pred_0 in I; apply (neq_succ_diag_l 0); exact I.
Qed.

Lemma le_pred_l n : P n <= n.
Proof.
  destruct (eq_decidable n 0) as [-> | H].
  - rewrite pred_0; exact (le_refl 0).
  - apply Private_succ_pred in H; rewrite <-H at 2; exact (le_succ_diag_r _).
Qed.

Include NZAddOrder.NatIntAddOrderProp N.

Theorem succ_pred n : n ~= 0 -> S (P n) == n.
Proof. exact (Private_succ_pred n). Qed.

Theorem le_0_l : forall n, 0 <= n.
Proof. exact (Private_nat_le_0_l pred_0). Qed.

Theorem neq_succ_0 : forall n, S n ~= 0.
Proof. exact (Private_nat_neq_succ_0 pred_0). Qed.

Theorem neq_0_succ : forall n, 0 ~= S n.
Proof. intros n; apply neq_sym; exact (neq_succ_0 _). Qed.

Theorem zero_or_succ n : n == 0 \/ exists m, n == S m.
Proof. exact (Private_nat_zero_or_succ pred_0 n). Qed.

Theorem induction :
  forall A : N.t -> Prop, Proper (N.eq==>iff) A ->
    A 0 -> (forall n, A n -> A (S n)) -> forall n, A n.
Proof. exact (Private_nat_induction pred_0). Qed.

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
Proof. intros H; exact (neq_succ_0 0 (H (S 0))). Qed.

Theorem neq_0_r n : n ~= 0 <-> exists m, n == S m.
Proof.
  split; [intros H%succ_pred | intros [m ->]; exact (neq_succ_0 _)].
  exists (P n); symmetry; exact H.
Qed.

Theorem eq_pred_0 n : P n == 0 <-> n == 0 \/ n == 1.
Proof.
  rewrite one_succ; split.
  - destruct (zero_or_succ n) as [-> | [m ->]]; [intros _; left; reflexivity |].
    rewrite pred_succ; intros ->; right; reflexivity.
  - intros [-> | ->]; [exact pred_0 | exact (pred_succ 0)].
Qed.

Theorem pred_inj n m : n ~= 0 -> m ~= 0 -> P n == P m -> n == m.
Proof. intros H%succ_pred K%succ_pred L; rewrite <-H, <-K, L; reflexivity. Qed.

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
intro n; induct n; [ | intros n [IH1 IH2]]; auto.
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
intros H1 H2 H3. intro n; induct n.
- intro m; induct m.
  + exact H1.
  + exact (H2 0).
- intros n IH. intro m; induct m.
  + now apply H3.
  + exact (H2 (S n)).
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
intros H1 H2 H3 n; induct n; auto.
intros n H m; cases m; auto.
Qed.

End DoubleInduction.

Ltac double_induct n m :=
  try intros until n;
  try intros until m;
  pattern n, m; apply double_induction; clear n m;
  [solve_proper | | | ].

End NBaseProp.

