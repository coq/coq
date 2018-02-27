(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase Rfunctions SeqSeries Rtrigo_fun Max.
Local Open Scope R_scope.

(********************************)
(** * Definition of exponential *)
(********************************)
Definition exp_in (x l:R) : Prop :=
  infinite_sum (fun i:nat => / INR (fact i) * x ^ i) l.

Lemma exp_cof_no_R0 : forall n:nat, / INR (fact n) <> 0.
Proof.
  intro.
  apply Rinv_neq_0_compat.
  apply INR_fact_neq_0.
Qed.

Lemma exist_exp : forall x:R, { l:R | exp_in x l }.
Proof.
  intro;
    generalize
      (Alembert_C3 (fun n:nat => / INR (fact n)) x exp_cof_no_R0 Alembert_exp).
  unfold Pser, exp_in.
  trivial.
Defined.

Definition exp (x:R) : R := proj1_sig (exist_exp x).

Lemma pow_i : forall i:nat, (0 < i)%nat -> 0 ^ i = 0.
Proof.
  intros; apply pow_ne_zero.
  red; intro; rewrite H0 in H; elim (lt_irrefl _ H).
Qed.

Lemma exist_exp0 : { l:R | exp_in 0 l }.
Proof.
  exists 1.
  unfold exp_in; unfold infinite_sum; intros.
  exists 0%nat.
  intros; replace (sum_f_R0 (fun i:nat => / INR (fact i) * 0 ^ i) n) with 1.
  unfold R_dist; replace (1 - 1) with 0;
    [ rewrite Rabs_R0; assumption | ring ].
  induction  n as [| n Hrecn].
  simpl; rewrite Rinv_1; ring.
  rewrite tech5.
  rewrite <- Hrecn.
  simpl.
  ring.
  unfold ge; apply le_O_n.
Defined.

(* Value of [exp 0] *)
Lemma exp_0 : exp 0 = 1.
Proof.
  cut (exp_in 0 (exp 0)).
  cut (exp_in 0 1).
  unfold exp_in; intros; eapply uniqueness_sum.
  apply H0.
  apply H.
  exact (proj2_sig exist_exp0).
  exact (proj2_sig (exist_exp 0)).
Qed.

(*****************************************)
(** * Definition of hyperbolic functions *)
(*****************************************)
Definition cosh (x:R) : R := (exp x + exp (- x)) / 2.
Definition sinh (x:R) : R := (exp x - exp (- x)) / 2.
Definition tanh (x:R) : R := sinh x / cosh x.

Lemma cosh_0 : cosh 0 = 1.
Proof.
  unfold cosh; rewrite Ropp_0; rewrite exp_0.
  unfold Rdiv; rewrite <- Rinv_r_sym; [ reflexivity | discrR ].
Qed.

Lemma sinh_0 : sinh 0 = 0.
Proof.
  unfold sinh; rewrite Ropp_0; rewrite exp_0.
  unfold Rminus, Rdiv; rewrite Rplus_opp_r; apply Rmult_0_l.
Qed.

Definition cos_n (n:nat) : R := (-1) ^ n / INR (fact (2 * n)).

Lemma simpl_cos_n :
  forall n:nat, cos_n (S n) / cos_n n = - / INR (2 * S n * (2 * n + 1)).
Proof.
  intro; unfold cos_n; replace (S n) with (n + 1)%nat; [ idtac | ring ].
  rewrite pow_add; unfold Rdiv; rewrite Rinv_mult_distr.
  rewrite Rinv_involutive.
  replace
  ((-1) ^ n * (-1) ^ 1 * / INR (fact (2 * (n + 1))) *
    (/ (-1) ^ n * INR (fact (2 * n)))) with
  ((-1) ^ n * / (-1) ^ n * / INR (fact (2 * (n + 1))) * INR (fact (2 * n)) *
    (-1) ^ 1); [ idtac | ring ].
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; unfold pow; rewrite Rmult_1_r.
  replace (2 * (n + 1))%nat with (S (S (2 * n))); [ idtac | ring ].
  do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
    repeat rewrite Rinv_mult_distr; try (apply not_O_INR; discriminate).
  rewrite <- (Rmult_comm (-1)).
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  replace (S (2 * n)) with (2 * n + 1)%nat; [ idtac | ring ].
  rewrite mult_INR; rewrite Rinv_mult_distr.
  ring.
  apply not_O_INR; discriminate.
  replace (2 * n + 1)%nat with (S (2 * n));
  [ apply not_O_INR; discriminate | ring ].
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply prod_neq_R0; [ apply not_O_INR; discriminate | apply INR_fact_neq_0 ].
  apply pow_nonzero; discrR.
  apply INR_fact_neq_0.
  apply pow_nonzero; discrR.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
Qed.

Lemma archimed_cor1 :
  forall eps:R, 0 < eps ->  exists N : nat, / INR N < eps /\ (0 < N)%nat.
Proof.
  intros; cut (/ eps < IZR (up (/ eps))).
  intro; cut (0 <= up (/ eps))%Z.
  intro; assert (H2 := IZN _ H1); elim H2; intros; exists (max x 1).
  split.
  cut (0 < IZR (Z.of_nat x)).
  intro; rewrite INR_IZR_INZ; apply Rle_lt_trans with (/ IZR (Z.of_nat x)).
  apply Rmult_le_reg_l with (IZR (Z.of_nat x)).
  assumption.
  rewrite <- Rinv_r_sym;
    [ idtac | red; intro; rewrite H5 in H4; elim (Rlt_irrefl _ H4) ].
  apply Rmult_le_reg_l with (IZR (Z.of_nat (max x 1))).
  apply Rlt_le_trans with (IZR (Z.of_nat x)).
  assumption.
  repeat rewrite <- INR_IZR_INZ; apply le_INR; apply le_max_l.
  rewrite Rmult_1_r; rewrite (Rmult_comm (IZR (Z.of_nat (max x 1))));
    rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; repeat rewrite <- INR_IZR_INZ; apply le_INR;
    apply le_max_l.
  rewrite <- INR_IZR_INZ; apply not_O_INR.
  red; intro; assert (H6 := le_max_r x 1); cut (0 < 1)%nat;
    [ intro | apply lt_O_Sn ]; assert (H8 := lt_le_trans _ _ _ H7 H6);
      rewrite H5 in H8; elim (lt_irrefl _ H8).
  pattern eps at 1; rewrite <- Rinv_involutive.
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; assumption | assumption ].
  rewrite H3 in H0; assumption.
  red; intro; rewrite H5 in H; elim (Rlt_irrefl _ H).
  apply Rlt_trans with (/ eps).
  apply Rinv_0_lt_compat; assumption.
  rewrite H3 in H0; assumption.
  apply lt_le_trans with 1%nat; [ apply lt_O_Sn | apply le_max_r ].
  apply le_IZR; left;
    apply Rlt_trans with (/ eps);
      [ apply Rinv_0_lt_compat; assumption | assumption ].
  assert (H0 := archimed (/ eps)).
  elim H0; intros; assumption.
Qed.

Lemma Alembert_cos : Un_cv (fun n:nat => Rabs (cos_n (S n) / cos_n n)) 0.
Proof.
  unfold Un_cv; intros.
  assert (H0 := archimed_cor1 eps H).
  elim H0; intros; exists x.
  intros; rewrite simpl_cos_n; unfold R_dist; unfold Rminus;
    rewrite Ropp_0; rewrite Rplus_0_r; rewrite Rabs_Rabsolu;
      rewrite Rabs_Ropp; rewrite Rabs_right.
  rewrite mult_INR; rewrite Rinv_mult_distr.
  cut (/ INR (2 * S n) < 1).
  intro; cut (/ INR (2 * n + 1) < eps).
  intro; rewrite <- (Rmult_1_l eps).
  apply Rmult_gt_0_lt_compat; try assumption.
  change (0 < / INR (2 * n + 1)); apply Rinv_0_lt_compat;
    apply lt_INR_0.
  replace (2 * n + 1)%nat with (S (2 * n)); [ apply lt_O_Sn | ring ].
  apply Rlt_0_1.
  cut (x < 2 * n + 1)%nat.
  intro; assert (H5 := lt_INR _ _ H4).
  apply Rlt_trans with (/ INR x).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply lt_INR_0.
  elim H1; intros; assumption.
  apply lt_INR_0; replace (2 * n + 1)%nat with (S (2 * n));
    [ apply lt_O_Sn | ring ].
  assumption.
  elim H1; intros; assumption.
  apply lt_le_trans with (S n).
  unfold ge in H2; apply le_lt_n_Sm; assumption.
  replace (2 * n + 1)%nat with (S (2 * n)) by ring.
  apply le_n_S; apply le_n_2n.
  apply Rmult_lt_reg_l with (INR (2 * S n)).
  apply lt_INR_0; replace (2 * S n)%nat with (S (S (2 * n))).
  apply lt_O_Sn.
  replace (S n) with (n + 1)%nat by ring.
  ring.
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r.
  apply (lt_INR 1).
  replace (2 * S n)%nat with (S (S (2 * n))).
  apply lt_n_S; apply lt_O_Sn.
  ring.
  apply not_O_INR; discriminate.
  apply not_O_INR; discriminate.
  replace (2 * n + 1)%nat with (S (2 * n));
  [ apply not_O_INR; discriminate | ring ].
  apply Rle_ge; left; apply Rinv_0_lt_compat.
  apply lt_INR_0.
  replace (2 * S n * (2 * n + 1))%nat with (2 + (4 * (n * n) + 6 * n))%nat by ring.
  apply lt_O_Sn.
Qed.

Lemma cosn_no_R0 : forall n:nat, cos_n n <> 0.
Proof.
  intro; unfold cos_n; unfold Rdiv; apply prod_neq_R0.
  apply pow_nonzero; discrR.
  apply Rinv_neq_0_compat.
  apply INR_fact_neq_0.
Qed.

(**********)
Definition cos_in (x l:R) : Prop :=
  infinite_sum (fun i:nat => cos_n i * x ^ i) l.

(**********)
Lemma exist_cos : forall x:R, { l:R | cos_in x l }.
Proof.
  intro; generalize (Alembert_C3 cos_n x cosn_no_R0 Alembert_cos).
  unfold Pser, cos_in; trivial.
Qed.


(** Definition of cosinus *)
Definition cos (x:R) : R := let (a,_) := exist_cos (Rsqr x) in a.

Definition sin_n (n:nat) : R := (-1) ^ n / INR (fact (2 * n + 1)).

Lemma simpl_sin_n :
  forall n:nat, sin_n (S n) / sin_n n = - / INR ((2 * S n + 1) * (2 * S n)).
Proof.
  intro; unfold sin_n; replace (S n) with (n + 1)%nat; [ idtac | ring ].
  rewrite pow_add; unfold Rdiv; rewrite Rinv_mult_distr.
  rewrite Rinv_involutive.
  replace
  ((-1) ^ n * (-1) ^ 1 * / INR (fact (2 * (n + 1) + 1)) *
    (/ (-1) ^ n * INR (fact (2 * n + 1)))) with
  ((-1) ^ n * / (-1) ^ n * / INR (fact (2 * (n + 1) + 1)) *
    INR (fact (2 * n + 1)) * (-1) ^ 1); [ idtac | ring ].
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; unfold pow; rewrite Rmult_1_r;
    replace (2 * (n + 1) + 1)%nat with (S (S (2 * n + 1))).
  do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
    repeat rewrite Rinv_mult_distr.
  rewrite <- (Rmult_comm (-1)); repeat rewrite Rmult_assoc;
    rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; replace (S (2 * n + 1)) with (2 * (n + 1))%nat.
  repeat rewrite mult_INR; repeat rewrite Rinv_mult_distr.
  ring.
  apply not_O_INR; discriminate.
  replace (n + 1)%nat with (S n); [ apply not_O_INR; discriminate | ring ].
  apply not_O_INR; discriminate.
  apply prod_neq_R0.
  apply not_O_INR; discriminate.
  replace (n + 1)%nat with (S n); [ apply not_O_INR; discriminate | ring ].
  apply not_O_INR; discriminate.
  replace (n + 1)%nat with (S n); [ apply not_O_INR; discriminate | ring ].
  rewrite mult_plus_distr_l; cut (forall n:nat, S n = (n + 1)%nat).
  intros; rewrite (H (2 * n + 1)%nat).
  ring.
  intros; ring.
  apply INR_fact_neq_0.
  apply not_O_INR; discriminate.
  apply INR_fact_neq_0.
  apply not_O_INR; discriminate.
  apply prod_neq_R0; [ apply not_O_INR; discriminate | apply INR_fact_neq_0 ].
  cut (forall n:nat, S (S n) = (n + 2)%nat);
    [ intros; rewrite (H (2 * n + 1)%nat); ring | intros; ring ].
  apply pow_nonzero; discrR.
  apply INR_fact_neq_0.
  apply pow_nonzero; discrR.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
Qed.

Lemma Alembert_sin : Un_cv (fun n:nat => Rabs (sin_n (S n) / sin_n n)) 0.
Proof.
  unfold Un_cv; intros; assert (H0 := archimed_cor1 eps H).
  elim H0; intros; exists x.
  intros; rewrite simpl_sin_n; unfold R_dist; unfold Rminus;
    rewrite Ropp_0; rewrite Rplus_0_r; rewrite Rabs_Rabsolu;
      rewrite Rabs_Ropp; rewrite Rabs_right.
  rewrite mult_INR; rewrite Rinv_mult_distr.
  cut (/ INR (2 * S n) < 1).
  intro; cut (/ INR (2 * S n + 1) < eps).
  intro; rewrite <- (Rmult_1_l eps); rewrite (Rmult_comm (/ INR (2 * S n + 1)));
    apply Rmult_gt_0_lt_compat; try assumption.
  change (0 < / INR (2 * S n + 1)); apply Rinv_0_lt_compat;
    apply lt_INR_0; replace (2 * S n + 1)%nat with (S (2 * S n));
      [ apply lt_O_Sn | ring ].
  apply Rlt_0_1.
  cut (x < 2 * S n + 1)%nat.
  intro; assert (H5 := lt_INR _ _ H4); apply Rlt_trans with (/ INR x).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply lt_INR_0; elim H1; intros; assumption.
  apply lt_INR_0; replace (2 * S n + 1)%nat with (S (2 * S n));
    [ apply lt_O_Sn | ring ].
  assumption.
  elim H1; intros; assumption.
  apply lt_le_trans with (S n).
  unfold ge in H2; apply le_lt_n_Sm; assumption.
  replace (2 * S n + 1)%nat with (S (2 * S n)) by ring.
  apply le_S; apply le_n_2n.
  apply Rmult_lt_reg_l with (INR (2 * S n)).
  apply lt_INR_0; replace (2 * S n)%nat with (S (S (2 * n)));
    [ apply lt_O_Sn | ring ].
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r.
  apply (lt_INR 1).
  replace (2 * S n)%nat with (S (S (2 * n))).
  apply lt_n_S; apply lt_O_Sn.
  ring.
  apply not_O_INR; discriminate.
  apply not_O_INR; discriminate.
  apply not_O_INR; discriminate.
  left; apply Rinv_0_lt_compat.
  apply lt_INR_0.
  replace ((2 * S n + 1) * (2 * S n))%nat with
  (6 + (4 * (n * n) + 10 * n))%nat by ring.
  apply lt_O_Sn.
Qed.

Lemma sin_no_R0 : forall n:nat, sin_n n <> 0.
Proof.
  intro; unfold sin_n; unfold Rdiv; apply prod_neq_R0.
  apply pow_nonzero; discrR.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
Qed.

(**********)
Definition sin_in (x l:R) : Prop :=
  infinite_sum (fun i:nat => sin_n i * x ^ i) l.

(**********)
Lemma exist_sin : forall x:R, { l:R | sin_in x l }.
Proof.
  intro; generalize (Alembert_C3 sin_n x sin_no_R0 Alembert_sin).
  unfold Pser, sin_n; trivial.
Defined.

(***********************)
(* Definition of sinus *)
Definition sin (x:R) : R := let (a,_) := exist_sin (Rsqr x) in x * a.

(*********************************************)
(** *              Properties                *)
(*********************************************)

Lemma cos_sym : forall x:R, cos x = cos (- x).
Proof.
  intros; unfold cos; replace (Rsqr (- x)) with (Rsqr x).
  reflexivity.
  apply Rsqr_neg.
Qed.

Lemma sin_antisym : forall x:R, sin (- x) = - sin x.
Proof.
  intro; unfold sin; replace (Rsqr (- x)) with (Rsqr x);
    [ idtac | apply Rsqr_neg ].
  case (exist_sin (Rsqr x)); intros; ring.
Qed.

Lemma sin_0 : sin 0 = 0.
Proof.
  unfold sin; case (exist_sin (Rsqr 0)).
  intros; ring.
Qed.

Lemma exist_cos0 : { l:R | cos_in 0 l }.
Proof.
  exists 1.
  unfold cos_in; unfold infinite_sum; intros; exists 0%nat.
  intros.
  unfold R_dist.
  induction  n as [| n Hrecn].
  unfold cos_n; simpl.
  unfold Rdiv; rewrite Rinv_1.
  do 2 rewrite Rmult_1_r.
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
  rewrite tech5.
  replace (cos_n (S n) * 0 ^ S n) with 0.
  rewrite Rplus_0_r.
  apply Hrecn; unfold ge; apply le_O_n.
  simpl; ring.
Defined.

(* Value of [cos 0] *)
Lemma cos_0 : cos 0 = 1.
Proof.
  cut (cos_in 0 (cos 0)).
  cut (cos_in 0 1).
  unfold cos_in; intros; eapply uniqueness_sum.
  apply H0.
  apply H.
  exact (proj2_sig exist_cos0).
  assert (H := proj2_sig (exist_cos (Rsqr 0))); unfold cos;
    pattern 0 at 1; replace 0 with (Rsqr 0); [ exact H | apply Rsqr_0 ].
Qed.
