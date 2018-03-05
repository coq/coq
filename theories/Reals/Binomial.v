(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import PartSum.
Local Open Scope R_scope.

Definition C (n p:nat) : R :=
  INR (fact n) / (INR (fact p) * INR (fact (n - p))).

Lemma pascal_step1 : forall n i:nat, (i <= n)%nat -> C n i = C n (n - i).
Proof.
  intros; unfold C; replace (n - (n - i))%nat with i.
  rewrite Rmult_comm.
  reflexivity.
  apply plus_minus; rewrite plus_comm; apply le_plus_minus; assumption.
Qed.

Lemma pascal_step2 :
  forall n i:nat,
    (i <= n)%nat -> C (S n) i = INR (S n) / INR (S n - i) * C n i.
Proof.
  intros; unfold C; replace (S n - i)%nat with (S (n - i)).
  cut (forall n:nat, fact (S n) = (S n * fact n)%nat).
  intro; repeat rewrite H0.
  unfold Rdiv; repeat rewrite mult_INR; repeat rewrite Rinv_mult_distr.
  ring.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply not_O_INR; discriminate.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply prod_neq_R0.
  apply not_O_INR; discriminate.
  apply INR_fact_neq_0.
  intro; reflexivity.
  apply minus_Sn_m; assumption.
Qed.

Lemma pascal_step3 :
  forall n i:nat, (i < n)%nat -> C n (S i) = INR (n - i) / INR (S i) * C n i.
Proof.
  intros; unfold C.
  cut (forall n:nat, fact (S n) = (S n * fact n)%nat).
  intro.
  cut ((n - i)%nat = S (n - S i)).
  intro.
  pattern (n - i)%nat at 2; rewrite H1.
  repeat rewrite H0; unfold Rdiv; repeat rewrite mult_INR;
    repeat rewrite Rinv_mult_distr.
  rewrite <- H1; rewrite (Rmult_comm (/ INR (n - i)));
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm (INR (n - i)));
      repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  ring.
  apply not_O_INR; apply minus_neq_O; assumption.
  apply not_O_INR; discriminate.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply prod_neq_R0; [ apply not_O_INR; discriminate | apply INR_fact_neq_0 ].
  apply not_O_INR; discriminate.
  apply INR_fact_neq_0.
  apply prod_neq_R0; [ apply not_O_INR; discriminate | apply INR_fact_neq_0 ].
  apply INR_fact_neq_0.
  rewrite minus_Sn_m.
  simpl; reflexivity.
  apply lt_le_S; assumption.
  intro; reflexivity.
Qed.

  (**********)
Lemma pascal :
  forall n i:nat, (i < n)%nat -> C n i + C n (S i) = C (S n) (S i).
Proof.
  intros.
  rewrite pascal_step3; [ idtac | assumption ].
  replace (C n i + INR (n - i) / INR (S i) * C n i) with
    (C n i * (1 + INR (n - i) / INR (S i))); [ idtac | ring ].
  replace (1 + INR (n - i) / INR (S i)) with (INR (S n) / INR (S i)).
  rewrite pascal_step1.
  rewrite Rmult_comm; replace (S i) with (S n - (n - i))%nat.
  rewrite <- pascal_step2.
  apply pascal_step1.
  apply le_trans with n.
  apply le_minusni_n.
  apply lt_le_weak; assumption.
  apply le_n_Sn.
  apply le_minusni_n.
  apply lt_le_weak; assumption.
  rewrite <- minus_Sn_m.
  cut ((n - (n - i))%nat = i).
  intro; rewrite H0; reflexivity.
  symmetry ; apply plus_minus.
  rewrite plus_comm; rewrite le_plus_minus_r.
  reflexivity.
  apply lt_le_weak; assumption.
  apply le_minusni_n; apply lt_le_weak; assumption.
  apply lt_le_weak; assumption.
  unfold Rdiv.
  repeat rewrite S_INR.
  rewrite minus_INR.
  cut (INR i + 1 <> 0).
  intro.
  apply Rmult_eq_reg_l with (INR i + 1); [ idtac | assumption ].
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  do 2 rewrite (Rmult_comm (INR i + 1)).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym; [ idtac | assumption ].
  ring.
  rewrite <- S_INR.
  apply not_O_INR; discriminate.
  apply lt_le_weak; assumption.
Qed.

  (*********************)
  (*********************)
Lemma binomial :
  forall (x y:R) (n:nat),
    (x + y) ^ n = sum_f_R0 (fun i:nat => C n i * x ^ i * y ^ (n - i)) n.
Proof.
  intros; induction  n as [| n Hrecn].
  unfold C; simpl; unfold Rdiv;
    repeat rewrite Rmult_1_r; rewrite Rinv_1; ring.
  pattern (S n) at 1; replace (S n) with (n + 1)%nat; [ idtac | ring ].
  rewrite pow_add; rewrite Hrecn.
  replace ((x + y) ^ 1) with (x + y); [ idtac | simpl; ring ].
  rewrite tech5.
  cut (forall p:nat, C p p = 1).
  cut (forall p:nat, C p 0 = 1).
  intros; rewrite H0; rewrite <- minus_n_n; rewrite Rmult_1_l.
  replace (y ^ 0) with 1; [ rewrite Rmult_1_r | simpl; reflexivity ].
  induction  n as [| n Hrecn0].
  simpl; do 2 rewrite H; ring.
  (* N >= 1 *)
  set (N := S n).
  rewrite Rmult_plus_distr_l.
  replace (sum_f_R0 (fun i:nat => C N i * x ^ i * y ^ (N - i)) N * x) with
    (sum_f_R0 (fun i:nat => C N i * x ^ S i * y ^ (N - i)) N).
  replace (sum_f_R0 (fun i:nat => C N i * x ^ i * y ^ (N - i)) N * y) with
    (sum_f_R0 (fun i:nat => C N i * x ^ i * y ^ (S N - i)) N).
  rewrite (decomp_sum (fun i:nat => C (S N) i * x ^ i * y ^ (S N - i)) N).
  rewrite H; replace (x ^ 0) with 1; [ idtac | reflexivity ].
  do 2 rewrite Rmult_1_l.
  replace (S N - 0)%nat with (S N); [ idtac | reflexivity ].
  set (An := fun i:nat => C N i * x ^ S i * y ^ (N - i)).
  set (Bn := fun i:nat => C N (S i) * x ^ S i * y ^ (N - i)).
  replace (pred N) with n.
  replace (sum_f_R0 (fun i:nat => C (S N) (S i) * x ^ S i * y ^ (S N - S i)) n)
    with (sum_f_R0 (fun i:nat => An i + Bn i) n).
  rewrite plus_sum.
  replace (x ^ S N) with (An (S n)).
  rewrite (Rplus_comm (sum_f_R0 An n)).
  repeat rewrite Rplus_assoc.
  rewrite <- tech5.
  fold N.
  set (Cn := fun i:nat => C N i * x ^ i * y ^ (S N - i)).
  cut (forall i:nat, (i < N)%nat -> Cn (S i) = Bn i).
  intro; replace (sum_f_R0 Bn n) with (sum_f_R0 (fun i:nat => Cn (S i)) n).
  replace (y ^ S N) with (Cn 0%nat).
  rewrite <- Rplus_assoc; rewrite (decomp_sum Cn N).
  replace (pred N) with n.
  ring.
  unfold N; simpl; reflexivity.
  unfold N; apply lt_O_Sn.
  unfold Cn; rewrite H; simpl; ring.
  apply sum_eq.
  intros; apply H1.
  unfold N; apply le_lt_trans with n; [ assumption | apply lt_n_Sn ].
  reflexivity.
  unfold An; fold N; rewrite <- minus_n_n; rewrite H0;
    simpl; ring.
  apply sum_eq.
  intros; unfold An, Bn.
  change (S N - S i)%nat with (N - i)%nat.
  rewrite <- pascal;
    [ ring
      | apply le_lt_trans with n; [ assumption | unfold N; apply lt_n_Sn ] ].
  unfold N; reflexivity.
  unfold N; apply lt_O_Sn.
  rewrite <- (Rmult_comm y); rewrite scal_sum; apply sum_eq.
  intros; replace (S N - i)%nat with (S (N - i)).
  replace (S (N - i)) with (N - i + 1)%nat; [ idtac | ring ].
  rewrite pow_add; replace (y ^ 1) with y; [ idtac | simpl; ring ];
    ring.
  apply minus_Sn_m; assumption.
  rewrite <- (Rmult_comm x); rewrite scal_sum; apply sum_eq.
  intros; replace (S i) with (i + 1)%nat; [ idtac | ring ]; rewrite pow_add;
    replace (x ^ 1) with x; [ idtac | simpl; ring ];
      ring.
  intro; unfold C.
  replace (INR (fact 0)) with 1; [ idtac | reflexivity ].
  replace (p - 0)%nat with p; [ idtac | apply minus_n_O ].
  rewrite Rmult_1_l; unfold Rdiv; rewrite <- Rinv_r_sym;
    [ reflexivity | apply INR_fact_neq_0 ].
  intro; unfold C.
  replace (p - p)%nat with 0%nat; [ idtac | apply minus_n_n ].
  replace (INR (fact 0)) with 1; [ idtac | reflexivity ].
  rewrite Rmult_1_r; unfold Rdiv; rewrite <- Rinv_r_sym;
    [ reflexivity | apply INR_fact_neq_0 ].
Qed.
