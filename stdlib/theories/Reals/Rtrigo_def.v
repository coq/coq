(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase Rfunctions SeqSeries Rtrigo_fun.
Require Import Arith.Factorial.
Require Import Lra Lia.
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
  red; intro; rewrite H0 in H; elim (Nat.lt_irrefl _ H).
Qed.

(* Value of [exp 0] *)
Lemma exp_0 : exp 0 = 1.
Proof.
  cut (exp_in 0 1).
  - cut (exp_in 0 (exp 0)).
    + apply uniqueness_sum.
    + exact (proj2_sig (exist_exp 0)).
  - unfold exp_in; unfold infinite_sum; intros.
    exists 0%nat.
    intros; replace (sum_f_R0 (fun i:nat => / INR (fact i) * 0 ^ i) n) with 1.
    + unfold Rdist; replace (1 - 1) with 0;
        [ rewrite Rabs_R0; assumption | ring ].
    + induction  n as [| n Hrecn].
      * simpl; rewrite Rinv_1; ring.
      * rewrite tech5.
        rewrite <- Hrecn.
        -- simpl.
           ring.
        -- unfold ge; apply Nat.le_0_l.
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
  unfold Rdiv; rewrite Rinv_r; [ reflexivity | discrR ].
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
  intro; unfold cos_n; replace (S n) with (n + 1)%nat by ring.
  rewrite pow_add; unfold Rdiv; rewrite Rinv_mult.
  rewrite Rinv_inv.
  replace
  ((-1) ^ n * (-1) ^ 1 * / INR (fact (2 * (n + 1))) *
    (/ (-1) ^ n * INR (fact (2 * n)))) with
  ((-1) ^ n * / (-1) ^ n * / INR (fact (2 * (n + 1))) * INR (fact (2 * n)) *
    (-1) ^ 1); [ idtac | ring ].
  rewrite Rinv_r.
  - rewrite Rmult_1_l; unfold pow; rewrite Rmult_1_r.
    replace (2 * (n + 1))%nat with (S (S (2 * n))) by ring.
    do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
    repeat rewrite Rinv_mult.
    rewrite <- (Rmult_comm (-1)).
    repeat rewrite Rmult_assoc; rewrite Rinv_l.
    + rewrite Rmult_1_r.
      replace (S (2 * n)) with (2 * n + 1)%nat by ring.
      rewrite mult_INR; rewrite Rinv_mult.
      ring.
    + apply INR_fact_neq_0.
  - apply pow_nonzero; discrR.
Qed.

Lemma archimed_cor1 :
  forall eps:R, 0 < eps ->  exists N : nat, / INR N < eps /\ (0 < N)%nat.
Proof.
  intros; assert (/ eps < IZR (up (/ eps))). {
    assert (H0 := archimed (/ eps)).
    elim H0; intros; assumption.
  }
  assert (0 <= up (/ eps))%Z. {
    apply le_IZR; left;
    apply Rlt_trans with (/ eps);
      [ apply Rinv_0_lt_compat; assumption | assumption ].
  }
  assert (H2 := IZN _ H1); elim H2; intros; exists (max x 1).
  split.
  - assert (0 < IZR (Z.of_nat x)). {
      apply Rlt_trans with (/ eps).
      - apply Rinv_0_lt_compat; assumption.
      - rewrite H3 in H0; assumption.
    }
    rewrite INR_IZR_INZ; apply Rle_lt_trans with (/ IZR (Z.of_nat x)).
    + apply Rmult_le_reg_l with (IZR (Z.of_nat x)).
      { assumption. }
      rewrite Rinv_r;
        [ idtac | red; intro; rewrite H5 in H4; elim (Rlt_irrefl _ H4) ].
      apply Rmult_le_reg_l with (IZR (Z.of_nat (max x 1))).
      * apply Rlt_le_trans with (IZR (Z.of_nat x)).
        -- assumption.
        -- repeat rewrite <- INR_IZR_INZ; apply le_INR; apply Nat.le_max_l.
      * rewrite Rmult_1_r; rewrite (Rmult_comm (IZR (Z.of_nat (max x 1))));
          rewrite Rmult_assoc; rewrite Rinv_l.
        -- rewrite Rmult_1_r; repeat rewrite <- INR_IZR_INZ; apply le_INR;
             apply Nat.le_max_l.
        -- rewrite <- INR_IZR_INZ; apply not_O_INR.
           red; intro; assert (H6 := Nat.le_max_r x 1); cut (0 < 1)%nat;
             [ intro | apply Nat.lt_0_succ ]; assert (H8 := Nat.lt_le_trans _ _ _ H7 H6);
             rewrite H5 in H8; elim (Nat.lt_irrefl _ H8).
    + pattern eps at 1; rewrite <- Rinv_inv.
      apply Rinv_lt_contravar.
      * apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; assumption | assumption ].
      * rewrite H3 in H0; assumption.
  - apply Nat.lt_le_trans with 1%nat; [ apply Nat.lt_0_succ | apply Nat.le_max_r ].
Qed.

Lemma Alembert_cos : Un_cv (fun n:nat => Rabs (cos_n (S n) / cos_n n)) 0.
Proof.
  unfold Un_cv; intros.
  assert (H0 := archimed_cor1 eps H).
  elim H0; intros; exists x.
  intros; rewrite simpl_cos_n; unfold Rdist; unfold Rminus;
    rewrite Ropp_0; rewrite Rplus_0_r; rewrite Rabs_Rabsolu;
      rewrite Rabs_Ropp; rewrite Rabs_right.
  2:{ apply Rle_ge; left; apply Rinv_0_lt_compat.
      apply lt_INR_0.
      replace (2 * S n * (2 * n + 1))%nat with (2 + (4 * (n * n) + 6 * n))%nat by ring.
      apply Nat.lt_0_succ. }
  rewrite mult_INR; rewrite Rinv_mult.
  assert (/ INR (2 * S n) < 1). {
    apply Rmult_lt_reg_l with (INR (2 * S n)).
    - apply lt_INR_0; replace (2 * S n)%nat with (S (S (2 * n))).
      + apply Nat.lt_0_succ.
      + replace (S n) with (n + 1)%nat by ring.
        ring.
    - rewrite Rinv_r.
      + rewrite Rmult_1_r.
        apply (lt_INR 1).
        nia.
      + apply not_O_INR; discriminate.
  }
  cut (/ INR (2 * n + 1) < eps).
  { intro; rewrite <- (Rmult_1_l eps).
    apply Rmult_gt_0_lt_compat; try assumption.
    - change (0 < / INR (2 * n + 1)); apply Rinv_0_lt_compat;
      apply lt_INR_0.
      replace (2 * n + 1)%nat with (S (2 * n)); [ apply Nat.lt_0_succ | ring ].
    - apply Rlt_0_1. }
  assert (x < 2 * n + 1)%nat by nia.
  assert (H5 := lt_INR _ _ H4).
  apply Rlt_trans with (/ INR x).
  2:{ elim H1; intros; assumption. }
  apply Rinv_lt_contravar.
  { apply Rmult_lt_0_compat.
    - apply lt_INR_0. nia.
    - apply lt_INR_0; nia.  }
  assumption.
Qed.

Lemma cosn_no_R0 : forall n:nat, cos_n n <> 0.
Proof.
  intro; unfold cos_n; unfold Rdiv; apply prod_neq_R0.
  - apply pow_nonzero; discrR.
  - apply Rinv_neq_0_compat.
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
  rewrite pow_add; unfold Rdiv; rewrite Rinv_mult.
  rewrite Rinv_inv.
  replace
  ((-1) ^ n * (-1) ^ 1 * / INR (fact (2 * (n + 1) + 1)) *
    (/ (-1) ^ n * INR (fact (2 * n + 1)))) with
  ((-1) ^ n * / (-1) ^ n * / INR (fact (2 * (n + 1) + 1)) *
    INR (fact (2 * n + 1)) * (-1) ^ 1); [ idtac | ring ].
  rewrite Rinv_r.
  2:{ apply pow_nonzero; discrR. }
  rewrite Rmult_1_l; unfold pow; rewrite Rmult_1_r;
    replace (2 * (n + 1) + 1)%nat with (S (S (2 * n + 1))) by nia.
  do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
  repeat rewrite Rinv_mult.
  rewrite <- (Rmult_comm (-1)); repeat rewrite Rmult_assoc;
    rewrite Rinv_l.
  - rewrite Rmult_1_r; replace (S (2 * n + 1)) with (2 * (n + 1))%nat by nia.
    repeat rewrite mult_INR; repeat rewrite Rinv_mult.
    ring.
  - apply INR_fact_neq_0.
Qed.

Lemma Alembert_sin : Un_cv (fun n:nat => Rabs (sin_n (S n) / sin_n n)) 0.
Proof.
  unfold Un_cv; intros; assert (H0 := archimed_cor1 eps H).
  elim H0; intros; exists x.
  intros; rewrite simpl_sin_n; unfold Rdist; unfold Rminus;
    rewrite Ropp_0; rewrite Rplus_0_r; rewrite Rabs_Rabsolu;
      rewrite Rabs_Ropp; rewrite Rabs_right.
  2:{ left; apply Rinv_0_lt_compat.
      apply lt_INR_0. nia. }
  rewrite mult_INR; rewrite Rinv_mult.
  assert (/ INR (2 * S n) < 1). {
    apply Rmult_lt_reg_l with (INR (2 * S n)).
    - apply lt_INR_0; replace (2 * S n)%nat with (S (S (2 * n)));
      [ apply Nat.lt_0_succ | ring ].
    - rewrite Rinv_r.
      + rewrite Rmult_1_r.
        apply (lt_INR 1). nia.
      + apply not_O_INR; discriminate.
  }
  cut (/ INR (2 * S n + 1) < eps).
  { intro; rewrite <- (Rmult_1_l eps); rewrite (Rmult_comm (/ INR (2 * S n + 1)));
      apply Rmult_gt_0_lt_compat; try assumption.
    - change (0 < / INR (2 * S n + 1)); apply Rinv_0_lt_compat;
      apply lt_INR_0; nia.
    - apply Rlt_0_1. }
  assert (x < 2 * S n + 1)%nat by nia.
  assert (H5 := lt_INR _ _ H4); apply Rlt_trans with (/ INR x).
  { apply Rinv_lt_contravar.
    - apply Rmult_lt_0_compat;apply lt_INR_0; nia.
    - assumption. }
  elim H1; intros; assumption.
Qed.

Lemma sin_no_R0 : forall n:nat, sin_n n <> 0.
Proof.
  intro; unfold sin_n; unfold Rdiv; apply prod_neq_R0.
  - apply pow_nonzero; discrR.
  - apply Rinv_neq_0_compat; apply INR_fact_neq_0.
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
  - reflexivity.
  - apply Rsqr_neg.
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

(* Value of [cos 0] *)
Lemma cos_0 : cos 0 = 1.
Proof.
  cut (cos_in 0 1).
  - cut (cos_in 0 (cos 0)).
    + apply uniqueness_sum.
    + rewrite <- Rsqr_0 at 1.
      exact (proj2_sig (exist_cos (Rsqr 0))).
  - unfold cos_in; unfold infinite_sum; intros; exists 0%nat.
    intros.
    unfold Rdist.
    induction  n as [| n Hrecn].
    + unfold cos_n; simpl.
      unfold Rdiv; rewrite Rinv_1.
      do 2 rewrite Rmult_1_r.
      unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
    + rewrite tech5.
      replace (cos_n (S n) * 0 ^ S n) with 0.
      * rewrite Rplus_0_r.
        apply Hrecn; unfold ge; apply Nat.le_0_l.
      * simpl; ring.
Qed.
