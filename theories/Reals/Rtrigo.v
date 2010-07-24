(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Export Rtrigo_fun.
Require Export Rtrigo_def.
Require Export Rtrigo_alt.
Require Export Cos_rel.
Require Export Cos_plus.
Require Import ZArith_base.
Require Import Zcomplements.
Require Import Classical_Prop.
Local Open Scope nat_scope.
Local Open Scope R_scope.

(** sin_PI2 is the only remaining axiom **)
Axiom sin_PI2 : sin (PI / 2) = 1.

(**********)
Lemma PI_neq0 : PI <> 0.
Proof.
  red in |- *; intro; assert (H0 := PI_RGT_0); rewrite H in H0;
    elim (Rlt_irrefl _ H0).
Qed.

(**********)
Lemma cos_minus : forall x y:R, cos (x - y) = cos x * cos y + sin x * sin y.
Proof.
  intros; unfold Rminus in |- *; rewrite cos_plus.
  rewrite <- cos_sym; rewrite sin_antisym; ring.
Qed.

(**********)
Lemma sin2_cos2 : forall x:R, Rsqr (sin x) + Rsqr (cos x) = 1.
Proof.
  intro; unfold Rsqr in |- *; rewrite Rplus_comm; rewrite <- (cos_minus x x);
    unfold Rminus in |- *; rewrite Rplus_opp_r; apply cos_0.
Qed.

Lemma cos2 : forall x:R, Rsqr (cos x) = 1 - Rsqr (sin x).
Proof.
  intro x; generalize (sin2_cos2 x); intro H1; rewrite <- H1;
    unfold Rminus in |- *; rewrite <- (Rplus_comm (Rsqr (cos x)));
      rewrite Rplus_assoc; rewrite Rplus_opp_r; symmetry  in |- *;
        apply Rplus_0_r.
Qed.

(**********)
Lemma cos_PI2 : cos (PI / 2) = 0.
Proof.
  apply Rsqr_eq_0; rewrite cos2; rewrite sin_PI2; rewrite Rsqr_1;
    unfold Rminus in |- *; apply Rplus_opp_r.
Qed.

(**********)
Lemma cos_PI : cos PI = -1.
Proof.
  replace PI with (PI / 2 + PI / 2).
  rewrite cos_plus.
  rewrite sin_PI2; rewrite cos_PI2.
  ring.
  symmetry  in |- *; apply double_var.
Qed.

Lemma sin_PI : sin PI = 0.
Proof.
  assert (H := sin2_cos2 PI).
  rewrite cos_PI in H.
  rewrite <- Rsqr_neg in H.
  rewrite Rsqr_1 in H.
  cut (Rsqr (sin PI) = 0).
  intro; apply (Rsqr_eq_0 _ H0).
  apply Rplus_eq_reg_l with 1.
  rewrite Rplus_0_r; rewrite Rplus_comm; exact H.
Qed.

(**********)
Lemma neg_cos : forall x:R, cos (x + PI) = - cos x.
Proof.
  intro x; rewrite cos_plus; rewrite sin_PI; rewrite cos_PI; ring.
Qed.

(**********)
Lemma sin_cos : forall x:R, sin x = - cos (PI / 2 + x).
Proof.
  intro x; rewrite cos_plus; rewrite sin_PI2; rewrite cos_PI2; ring.
Qed.

(**********)
Lemma sin_plus : forall x y:R, sin (x + y) = sin x * cos y + cos x * sin y.
Proof.
  intros.
  rewrite (sin_cos (x + y)).
  replace (PI / 2 + (x + y)) with (PI / 2 + x + y); [ rewrite cos_plus | ring ].
  rewrite (sin_cos (PI / 2 + x)).
  replace (PI / 2 + (PI / 2 + x)) with (x + PI).
  rewrite neg_cos.
  replace (cos (PI / 2 + x)) with (- sin x).
  ring.
  rewrite sin_cos; rewrite Ropp_involutive; reflexivity.
  pattern PI at 1 in |- *; rewrite (double_var PI); ring.
Qed.

Lemma sin_minus : forall x y:R, sin (x - y) = sin x * cos y - cos x * sin y.
Proof.
  intros; unfold Rminus in |- *; rewrite sin_plus.
  rewrite <- cos_sym; rewrite sin_antisym; ring.
Qed.

(**********)
Definition tan (x:R) : R := sin x / cos x.

Lemma tan_plus :
  forall x y:R,
    cos x <> 0 ->
    cos y <> 0 ->
    cos (x + y) <> 0 ->
    1 - tan x * tan y <> 0 ->
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof.
  intros; unfold tan in |- *; rewrite sin_plus; rewrite cos_plus;
    unfold Rdiv in |- *;
      replace (cos x * cos y - sin x * sin y) with
      (cos x * cos y * (1 - sin x * / cos x * (sin y * / cos y))).
  rewrite Rinv_mult_distr.
  repeat rewrite <- Rmult_assoc;
    replace ((sin x * cos y + cos x * sin y) * / (cos x * cos y)) with
    (sin x * / cos x + sin y * / cos y).
  reflexivity.
  rewrite Rmult_plus_distr_r; rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc; repeat rewrite (Rmult_comm (sin x));
    repeat rewrite <- Rmult_assoc.
  repeat rewrite Rinv_r_simpl_m; [ reflexivity | assumption | assumption ].
  assumption.
  assumption.
  apply prod_neq_R0; assumption.
  assumption.
  unfold Rminus in |- *; rewrite Rmult_plus_distr_l; rewrite Rmult_1_r;
    apply Rplus_eq_compat_l; repeat rewrite Rmult_assoc;
      rewrite (Rmult_comm (sin x)); rewrite (Rmult_comm (cos y));
        rewrite <- Ropp_mult_distr_r_reverse; repeat rewrite <- Rmult_assoc;
          rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; rewrite (Rmult_comm (sin x));
    rewrite <- Ropp_mult_distr_r_reverse; repeat rewrite Rmult_assoc;
      apply Rmult_eq_compat_l; rewrite (Rmult_comm (/ cos y));
        rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  apply Rmult_1_r.
  assumption.
  assumption.
Qed.

(*******************************************************)
(** * Some properties of cos, sin and tan              *)
(*******************************************************)

Lemma sin2 : forall x:R, Rsqr (sin x) = 1 - Rsqr (cos x).
Proof.
  intro x; generalize (cos2 x); intro H1; rewrite H1.
  unfold Rminus in |- *; rewrite Ropp_plus_distr; rewrite <- Rplus_assoc;
    rewrite Rplus_opp_r; rewrite Rplus_0_l; symmetry  in |- *;
      apply Ropp_involutive.
Qed.

Lemma sin_2a : forall x:R, sin (2 * x) = 2 * sin x * cos x.
Proof.
  intro x; rewrite double; rewrite sin_plus.
  rewrite <- (Rmult_comm (sin x)); symmetry  in |- *; rewrite Rmult_assoc;
    apply double.
Qed.

Lemma cos_2a : forall x:R, cos (2 * x) = cos x * cos x - sin x * sin x.
Proof.
  intro x; rewrite double; apply cos_plus.
Qed.

Lemma cos_2a_cos : forall x:R, cos (2 * x) = 2 * cos x * cos x - 1.
Proof.
  intro x; rewrite double; unfold Rminus in |- *; rewrite Rmult_assoc;
    rewrite cos_plus; generalize (sin2_cos2 x); rewrite double;
      intro H1; rewrite <- H1; ring_Rsqr.
Qed.

Lemma cos_2a_sin : forall x:R, cos (2 * x) = 1 - 2 * sin x * sin x.
Proof.
  intro x; rewrite Rmult_assoc; unfold Rminus in |- *; repeat rewrite double.
  generalize (sin2_cos2 x); intro H1; rewrite <- H1; rewrite cos_plus;
    ring_Rsqr.
Qed.

Lemma tan_2a :
  forall x:R,
    cos x <> 0 ->
    cos (2 * x) <> 0 ->
    1 - tan x * tan x <> 0 -> tan (2 * x) = 2 * tan x / (1 - tan x * tan x).
Proof.
  repeat rewrite double; intros; repeat rewrite double; rewrite double in H0;
    apply tan_plus; assumption.
Qed.

Lemma sin_neg : forall x:R, sin (- x) = - sin x.
Proof.
  apply sin_antisym.
Qed.

Lemma cos_neg : forall x:R, cos (- x) = cos x.
Proof.
  intro; symmetry  in |- *; apply cos_sym.
Qed.

Lemma tan_0 : tan 0 = 0.
Proof.
  unfold tan in |- *; rewrite sin_0; rewrite cos_0.
  unfold Rdiv in |- *; apply Rmult_0_l.
Qed.

Lemma tan_neg : forall x:R, tan (- x) = - tan x.
Proof.
  intros x; unfold tan in |- *; rewrite sin_neg; rewrite cos_neg;
    unfold Rdiv in |- *.
  apply Ropp_mult_distr_l_reverse.
Qed.

Lemma tan_minus :
  forall x y:R,
    cos x <> 0 ->
    cos y <> 0 ->
    cos (x - y) <> 0 ->
    1 + tan x * tan y <> 0 ->
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y).
Proof.
  intros; unfold Rminus in |- *; rewrite tan_plus.
  rewrite tan_neg; unfold Rminus in |- *; rewrite <- Ropp_mult_distr_l_reverse;
    rewrite Rmult_opp_opp; reflexivity.
  assumption.
  rewrite cos_neg; assumption.
  assumption.
  rewrite tan_neg; unfold Rminus in |- *; rewrite <- Ropp_mult_distr_l_reverse;
    rewrite Rmult_opp_opp; assumption.
Qed.

Lemma cos_3PI2 : cos (3 * (PI / 2)) = 0.
Proof.
  replace (3 * (PI / 2)) with (PI + PI / 2).
  rewrite cos_plus; rewrite sin_PI; rewrite cos_PI2; ring.
  pattern PI at 1 in |- *; rewrite (double_var PI).
  ring.
Qed.

Lemma sin_2PI : sin (2 * PI) = 0.
Proof.
  rewrite sin_2a; rewrite sin_PI; ring.
Qed.

Lemma cos_2PI : cos (2 * PI) = 1.
Proof.
  rewrite cos_2a; rewrite sin_PI; rewrite cos_PI; ring.
Qed.

Lemma neg_sin : forall x:R, sin (x + PI) = - sin x.
Proof.
  intro x; rewrite sin_plus; rewrite sin_PI; rewrite cos_PI; ring.
Qed.

Lemma sin_PI_x : forall x:R, sin (PI - x) = sin x.
Proof.
  intro x; rewrite sin_minus; rewrite sin_PI; rewrite cos_PI; rewrite Rmult_0_l;
    unfold Rminus in |- *; rewrite Rplus_0_l; rewrite Ropp_mult_distr_l_reverse;
      rewrite Ropp_involutive; apply Rmult_1_l.
Qed.

Lemma sin_period : forall (x:R) (k:nat), sin (x + 2 * INR k * PI) = sin x.
Proof.
  intros x k; induction  k as [| k Hreck].
  simpl in |- *;  ring_simplify (x + 2 * 0 * PI).
  trivial.

  replace (x + 2 * INR (S k) * PI) with (x + 2 * INR k * PI + 2 * PI).
  rewrite sin_plus in |- *; rewrite sin_2PI in |- *; rewrite cos_2PI in |- *.
  ring_simplify; trivial.
  rewrite S_INR in |- *;  ring.
Qed.

Lemma cos_period : forall (x:R) (k:nat), cos (x + 2 * INR k * PI) = cos x.
Proof.
  intros x k; induction  k as [| k Hreck].
  simpl in |- *;  ring_simplify (x + 2 * 0 * PI).
  trivial.

  replace (x + 2 * INR (S k) * PI) with (x + 2 * INR k * PI + 2 * PI).
  rewrite cos_plus in |- *; rewrite sin_2PI in |- *; rewrite cos_2PI in |- *.
  ring_simplify; trivial.
  rewrite S_INR in |- *;  ring.
Qed.

Lemma sin_shift : forall x:R, sin (PI / 2 - x) = cos x.
Proof.
  intro x; rewrite sin_minus; rewrite sin_PI2; rewrite cos_PI2; ring.
Qed.

Lemma cos_shift : forall x:R, cos (PI / 2 - x) = sin x.
Proof.
  intro x; rewrite cos_minus; rewrite sin_PI2; rewrite cos_PI2; ring.
Qed.

Lemma cos_sin : forall x:R, cos x = sin (PI / 2 + x).
Proof.
  intro x; rewrite sin_plus; rewrite sin_PI2; rewrite cos_PI2; ring.
Qed.

Lemma PI2_RGT_0 : 0 < PI / 2.
Proof.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply PI_RGT_0 | apply Rinv_0_lt_compat; prove_sup ].
Qed.

Lemma SIN_bound : forall x:R, -1 <= sin x <= 1.
Proof.
  intro; case (Rle_dec (-1) (sin x)); intro.
  case (Rle_dec (sin x) 1); intro.
  split; assumption.
  cut (1 < sin x).
  intro;
    generalize
      (Rsqr_incrst_1 1 (sin x) H (Rlt_le 0 1 Rlt_0_1)
        (Rlt_le 0 (sin x) (Rlt_trans 0 1 (sin x) Rlt_0_1 H)));
      rewrite Rsqr_1; intro; rewrite sin2 in H0; unfold Rminus in H0;
        generalize (Rplus_lt_compat_l (-1) 1 (1 + - Rsqr (cos x)) H0);
          repeat rewrite <- Rplus_assoc; repeat rewrite Rplus_opp_l;
            rewrite Rplus_0_l; intro; rewrite <- Ropp_0 in H1;
              generalize (Ropp_lt_gt_contravar (-0) (- Rsqr (cos x)) H1);
                repeat rewrite Ropp_involutive; intro; generalize (Rle_0_sqr (cos x));
                  intro; elim (Rlt_irrefl 0 (Rle_lt_trans 0 (Rsqr (cos x)) 0 H3 H2)).
  auto with real.
  cut (sin x < -1).
  intro; generalize (Ropp_lt_gt_contravar (sin x) (-1) H);
    rewrite Ropp_involutive; clear H; intro;
      generalize
        (Rsqr_incrst_1 1 (- sin x) H (Rlt_le 0 1 Rlt_0_1)
          (Rlt_le 0 (- sin x) (Rlt_trans 0 1 (- sin x) Rlt_0_1 H)));
        rewrite Rsqr_1; intro; rewrite <- Rsqr_neg in H0;
          rewrite sin2 in H0; unfold Rminus in H0;
            generalize (Rplus_lt_compat_l (-1) 1 (1 + - Rsqr (cos x)) H0);
              repeat rewrite <- Rplus_assoc; repeat rewrite Rplus_opp_l;
                rewrite Rplus_0_l; intro; rewrite <- Ropp_0 in H1;
                  generalize (Ropp_lt_gt_contravar (-0) (- Rsqr (cos x)) H1);
                    repeat rewrite Ropp_involutive; intro; generalize (Rle_0_sqr (cos x));
                      intro; elim (Rlt_irrefl 0 (Rle_lt_trans 0 (Rsqr (cos x)) 0 H3 H2)).
  auto with real.
Qed.

Lemma COS_bound : forall x:R, -1 <= cos x <= 1.
Proof.
  intro; rewrite <- sin_shift; apply SIN_bound.
Qed.

Lemma cos_sin_0 : forall x:R, ~ (cos x = 0 /\ sin x = 0).
Proof.
  intro; red in |- *; intro; elim H; intros; generalize (sin2_cos2 x); intro;
    rewrite H0 in H2; rewrite H1 in H2; repeat rewrite Rsqr_0 in H2;
      rewrite Rplus_0_r in H2; generalize Rlt_0_1; intro;
        rewrite <- H2 in H3; elim (Rlt_irrefl 0 H3).
Qed.

Lemma cos_sin_0_var : forall x:R, cos x <> 0 \/ sin x <> 0.
Proof.
  intro; apply not_and_or; apply cos_sin_0.
Qed.

(*****************************************************************)
(** * Using series definitions of cos and sin                    *)
(*****************************************************************)

Definition sin_lb (a:R) : R := sin_approx a 3.
Definition sin_ub (a:R) : R := sin_approx a 4.
Definition cos_lb (a:R) : R := cos_approx a 3.
Definition cos_ub (a:R) : R := cos_approx a 4.

Lemma sin_lb_gt_0 : forall a:R, 0 < a -> a <= PI / 2 -> 0 < sin_lb a.
Proof.
  intros.
  unfold sin_lb in |- *; unfold sin_approx in |- *; unfold sin_term in |- *.
  set (Un := fun i:nat => a ^ (2 * i + 1) / INR (fact (2 * i + 1))).
  replace
  (sum_f_R0
    (fun i:nat => (-1) ^ i * (a ^ (2 * i + 1) / INR (fact (2 * i + 1)))) 3)
    with (sum_f_R0 (fun i:nat => (-1) ^ i * Un i) 3);
      [ idtac | apply sum_eq; intros; unfold Un in |- *; reflexivity ].
  cut (forall n:nat, Un (S n) < Un n).
  intro; simpl in |- *.
  repeat rewrite Rmult_1_l; repeat rewrite Rmult_1_r;
    replace (-1 * Un 1%nat) with (- Un 1%nat); [ idtac | ring ];
    replace (-1 * -1 * Un 2%nat) with (Un 2%nat); [ idtac | ring ];
    replace (-1 * (-1 * -1) * Un 3%nat) with (- Un 3%nat);
    [ idtac | ring ];
    replace (Un 0%nat + - Un 1%nat + Un 2%nat + - Un 3%nat) with
    (Un 0%nat - Un 1%nat + (Un 2%nat - Un 3%nat)); [ idtac | ring ].
  apply Rplus_lt_0_compat.
  unfold Rminus in |- *; apply Rplus_lt_reg_r with (Un 1%nat);
    rewrite Rplus_0_r; rewrite (Rplus_comm (Un 1%nat));
      rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
        apply H1.
  unfold Rminus in |- *; apply Rplus_lt_reg_r with (Un 3%nat);
    rewrite Rplus_0_r; rewrite (Rplus_comm (Un 3%nat));
      rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
        apply H1.
  intro; unfold Un in |- *.
  cut ((2 * S n + 1)%nat = (2 * n + 1 + 2)%nat).
  intro; rewrite H1.
  rewrite pow_add; unfold Rdiv in |- *; rewrite Rmult_assoc;
    apply Rmult_lt_compat_l.
  apply pow_lt; assumption.
  rewrite <- H1; apply Rmult_lt_reg_l with (INR (fact (2 * n + 1))).
  apply lt_INR_0; apply neq_O_lt.
  assert (H2 := fact_neq_0 (2 * n + 1)).
  red in |- *; intro; elim H2; symmetry  in |- *; assumption.
  rewrite <- Rinv_r_sym.
  apply Rmult_lt_reg_l with (INR (fact (2 * S n + 1))).
  apply lt_INR_0; apply neq_O_lt.
  assert (H2 := fact_neq_0 (2 * S n + 1)).
  red in |- *; intro; elim H2; symmetry  in |- *; assumption.
  rewrite (Rmult_comm (INR (fact (2 * S n + 1)))); repeat rewrite Rmult_assoc;
    rewrite <- Rinv_l_sym.
  do 2 rewrite Rmult_1_r; apply Rle_lt_trans with (INR (fact (2 * n + 1)) * 4).
  apply Rmult_le_compat_l.
  replace 0 with (INR 0); [ idtac | reflexivity ]; apply le_INR; apply le_O_n.
  simpl in |- *; rewrite Rmult_1_r; replace 4 with (Rsqr 2);
    [ idtac | ring_Rsqr ]; replace (a * a) with (Rsqr a);
    [ idtac | reflexivity ]; apply Rsqr_incr_1.
  apply Rle_trans with (PI / 2);
    [ assumption
      | unfold Rdiv in |- *; apply Rmult_le_reg_l with 2;
        [ prove_sup0
          | rewrite <- Rmult_assoc; rewrite Rinv_r_simpl_m;
            [ replace 4 with 4; [ apply PI_4 | ring ] | discrR ] ] ].
  left; assumption.
  left; prove_sup0.
  rewrite H1; replace (2 * n + 1 + 2)%nat with (S (S (2 * n + 1))).
  do 2 rewrite fact_simpl; do 2 rewrite mult_INR.
  repeat rewrite <- Rmult_assoc.
  rewrite <- (Rmult_comm (INR (fact (2 * n + 1)))).
  rewrite Rmult_assoc.
  apply Rmult_lt_compat_l.
  apply lt_INR_0; apply neq_O_lt.
  assert (H2 := fact_neq_0 (2 * n + 1)).
  red in |- *; intro; elim H2; symmetry  in |- *; assumption.
  do 2 rewrite S_INR; rewrite plus_INR; rewrite mult_INR; set (x := INR n);
    unfold INR in |- *.
  replace ((2 * x + 1 + 1 + 1) * (2 * x + 1 + 1)) with (4 * x * x + 10 * x + 6);
  [ idtac | ring ].
  apply Rplus_lt_reg_r with (-4); rewrite Rplus_opp_l;
    replace (-4 + (4 * x * x + 10 * x + 6)) with (4 * x * x + 10 * x + 2);
    [ idtac | ring ].
  apply Rplus_le_lt_0_compat.
  cut (0 <= x).
  intro; apply Rplus_le_le_0_compat; repeat apply Rmult_le_pos;
    assumption || left; prove_sup.
  unfold x in |- *; replace 0 with (INR 0);
    [ apply le_INR; apply le_O_n | reflexivity ].
  prove_sup0.
  ring.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  ring.
Qed.

Lemma SIN : forall a:R, 0 <= a -> a <= PI -> sin_lb a <= sin a <= sin_ub a.
  intros; unfold sin_lb, sin_ub in |- *; apply (sin_bound a 1 H H0).
Qed.

Lemma COS :
  forall a:R, - PI / 2 <= a -> a <= PI / 2 -> cos_lb a <= cos a <= cos_ub a.
  intros; unfold cos_lb, cos_ub in |- *; apply (cos_bound a 1 H H0).
Qed.

(**********)
Lemma _PI2_RLT_0 : - (PI / 2) < 0.
Proof.
  rewrite <- Ropp_0; apply Ropp_lt_contravar; apply PI2_RGT_0.
Qed.

Lemma PI4_RLT_PI2 : PI / 4 < PI / 2.
Proof.
  unfold Rdiv in |- *; apply Rmult_lt_compat_l.
  apply PI_RGT_0.
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat; prove_sup0.
  pattern 2 at 1 in |- *; rewrite <- Rplus_0_r.
  replace 4 with (2 + 2); [ apply Rplus_lt_compat_l; prove_sup0 | ring ].
Qed.

Lemma PI2_Rlt_PI : PI / 2 < PI.
Proof.
  unfold Rdiv in |- *; pattern PI at 2 in |- *; rewrite <- Rmult_1_r.
  apply Rmult_lt_compat_l.
  apply PI_RGT_0.
  pattern 1 at 3 in |- *; rewrite <- Rinv_1; apply Rinv_lt_contravar.
  rewrite Rmult_1_l; prove_sup0.
  pattern 1 at 1 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l;
    apply Rlt_0_1.
Qed.

(***************************************************)
(** * Increasing and decreasing of [cos] and [sin] *)
(***************************************************)
Theorem sin_gt_0 : forall x:R, 0 < x -> x < PI -> 0 < sin x.
Proof.
  intros; elim (SIN x (Rlt_le 0 x H) (Rlt_le x PI H0)); intros H1 _;
    case (Rtotal_order x (PI / 2)); intro H2.
  apply Rlt_le_trans with (sin_lb x).
  apply sin_lb_gt_0; [ assumption | left; assumption ].
  assumption.
  elim H2; intro H3.
  rewrite H3; rewrite sin_PI2; apply Rlt_0_1.
  rewrite <- sin_PI_x; generalize (Ropp_gt_lt_contravar x (PI / 2) H3);
    intro H4; generalize (Rplus_lt_compat_l PI (- x) (- (PI / 2)) H4).
  replace (PI + - x) with (PI - x).
  replace (PI + - (PI / 2)) with (PI / 2).
  intro H5; generalize (Ropp_lt_gt_contravar x PI H0); intro H6;
    change (- PI < - x) in H6; generalize (Rplus_lt_compat_l PI (- PI) (- x) H6).
  rewrite Rplus_opp_r.
  replace (PI + - x) with (PI - x).
  intro H7;
    elim
      (SIN (PI - x) (Rlt_le 0 (PI - x) H7)
        (Rlt_le (PI - x) PI (Rlt_trans (PI - x) (PI / 2) PI H5 PI2_Rlt_PI)));
      intros H8 _;
        generalize (sin_lb_gt_0 (PI - x) H7 (Rlt_le (PI - x) (PI / 2) H5));
          intro H9; apply (Rlt_le_trans 0 (sin_lb (PI - x)) (sin (PI - x)) H9 H8).
  reflexivity.
  pattern PI at 2 in |- *; rewrite double_var; ring.
  reflexivity.
Qed.

Theorem cos_gt_0 : forall x:R, - (PI / 2) < x -> x < PI / 2 -> 0 < cos x.
Proof.
  intros; rewrite cos_sin;
    generalize (Rplus_lt_compat_l (PI / 2) (- (PI / 2)) x H).
  rewrite Rplus_opp_r; intro H1;
    generalize (Rplus_lt_compat_l (PI / 2) x (PI / 2) H0);
      rewrite <- double_var; intro H2; apply (sin_gt_0 (PI / 2 + x) H1 H2).
Qed.

Lemma sin_ge_0 : forall x:R, 0 <= x -> x <= PI -> 0 <= sin x.
Proof.
  intros x H1 H2; elim H1; intro H3;
    [ elim H2; intro H4;
      [ left; apply (sin_gt_0 x H3 H4)
        | rewrite H4; right; symmetry  in |- *; apply sin_PI ]
      | rewrite <- H3; right; symmetry  in |- *; apply sin_0 ].
Qed.

Lemma cos_ge_0 : forall x:R, - (PI / 2) <= x -> x <= PI / 2 -> 0 <= cos x.
Proof.
  intros x H1 H2; elim H1; intro H3;
    [ elim H2; intro H4;
      [ left; apply (cos_gt_0 x H3 H4)
        | rewrite H4; right; symmetry  in |- *; apply cos_PI2 ]
      | rewrite <- H3; rewrite cos_neg; right; symmetry  in |- *; apply cos_PI2 ].
Qed.

Lemma sin_le_0 : forall x:R, PI <= x -> x <= 2 * PI -> sin x <= 0.
Proof.
  intros x H1 H2; apply Rge_le; rewrite <- Ropp_0;
    rewrite <- (Ropp_involutive (sin x)); apply Ropp_le_ge_contravar;
      rewrite <- neg_sin; replace (x + PI) with (x - PI + 2 * INR 1 * PI);
        [ rewrite (sin_period (x - PI) 1); apply sin_ge_0;
          [ replace (x - PI) with (x + - PI);
            [ rewrite Rplus_comm; replace 0 with (- PI + PI);
              [ apply Rplus_le_compat_l; assumption | ring ]
              | ring ]
            | replace (x - PI) with (x + - PI); rewrite Rplus_comm;
              [ pattern PI at 2 in |- *; replace PI with (- PI + 2 * PI);
                [ apply Rplus_le_compat_l; assumption | ring ]
                | ring ] ]
          | unfold INR in |- *; ring ].
Qed.

Lemma cos_le_0 : forall x:R, PI / 2 <= x -> x <= 3 * (PI / 2) -> cos x <= 0.
Proof.
  intros x H1 H2; apply Rge_le; rewrite <- Ropp_0;
    rewrite <- (Ropp_involutive (cos x)); apply Ropp_le_ge_contravar;
      rewrite <- neg_cos; replace (x + PI) with (x - PI + 2 * INR 1 * PI).
  rewrite cos_period; apply cos_ge_0.
  replace (- (PI / 2)) with (- PI + PI / 2).
  unfold Rminus in |- *; rewrite (Rplus_comm x); apply Rplus_le_compat_l;
    assumption.
  pattern PI at 1 in |- *; rewrite (double_var PI); rewrite Ropp_plus_distr;
    ring.
  unfold Rminus in |- *; rewrite Rplus_comm;
    replace (PI / 2) with (- PI + 3 * (PI / 2)).
  apply Rplus_le_compat_l; assumption.
  pattern PI at 1 in |- *; rewrite (double_var PI); rewrite Ropp_plus_distr;
    ring.
  unfold INR in |- *; ring.
Qed.

Lemma sin_lt_0 : forall x:R, PI < x -> x < 2 * PI -> sin x < 0.
Proof.
  intros x H1 H2; rewrite <- Ropp_0; rewrite <- (Ropp_involutive (sin x));
    apply Ropp_lt_gt_contravar; rewrite <- neg_sin;
      replace (x + PI) with (x - PI + 2 * INR 1 * PI);
      [ rewrite (sin_period (x - PI) 1); apply sin_gt_0;
        [ replace (x - PI) with (x + - PI);
          [ rewrite Rplus_comm; replace 0 with (- PI + PI);
            [ apply Rplus_lt_compat_l; assumption | ring ]
            | ring ]
          | replace (x - PI) with (x + - PI); rewrite Rplus_comm;
            [ pattern PI at 2 in |- *; replace PI with (- PI + 2 * PI);
              [ apply Rplus_lt_compat_l; assumption | ring ]
              | ring ] ]
        | unfold INR in |- *; ring ].
Qed.

Lemma sin_lt_0_var : forall x:R, - PI < x -> x < 0 -> sin x < 0.
Proof.
  intros; generalize (Rplus_lt_compat_l (2 * PI) (- PI) x H);
    replace (2 * PI + - PI) with PI;
    [ intro H1; rewrite Rplus_comm in H1;
      generalize (Rplus_lt_compat_l (2 * PI) x 0 H0);
        intro H2; rewrite (Rplus_comm (2 * PI)) in H2;
          rewrite <- (Rplus_comm 0) in H2; rewrite Rplus_0_l in H2;
            rewrite <- (sin_period x 1); unfold INR in |- *;
              replace (2 * 1 * PI) with (2 * PI);
              [ apply (sin_lt_0 (x + 2 * PI) H1 H2) | ring ]
      | ring ].
Qed.

Lemma cos_lt_0 : forall x:R, PI / 2 < x -> x < 3 * (PI / 2) -> cos x < 0.
Proof.
  intros x H1 H2; rewrite <- Ropp_0; rewrite <- (Ropp_involutive (cos x));
    apply Ropp_lt_gt_contravar; rewrite <- neg_cos;
      replace (x + PI) with (x - PI + 2 * INR 1 * PI).
  rewrite cos_period; apply cos_gt_0.
  replace (- (PI / 2)) with (- PI + PI / 2).
  unfold Rminus in |- *; rewrite (Rplus_comm x); apply Rplus_lt_compat_l;
    assumption.
  pattern PI at 1 in |- *; rewrite (double_var PI); rewrite Ropp_plus_distr;
    ring.
  unfold Rminus in |- *; rewrite Rplus_comm;
    replace (PI / 2) with (- PI + 3 * (PI / 2)).
  apply Rplus_lt_compat_l; assumption.
  pattern PI at 1 in |- *; rewrite (double_var PI); rewrite Ropp_plus_distr;
    ring.
  unfold INR in |- *; ring.
Qed.

Lemma tan_gt_0 : forall x:R, 0 < x -> x < PI / 2 -> 0 < tan x.
Proof.
  intros x H1 H2; unfold tan in |- *; generalize _PI2_RLT_0;
    generalize (Rlt_trans 0 x (PI / 2) H1 H2); intros;
      generalize (Rlt_trans (- (PI / 2)) 0 x H0 H1); intro H5;
        generalize (Rlt_trans x (PI / 2) PI H2 PI2_Rlt_PI);
          intro H7; unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  apply sin_gt_0; assumption.
  apply Rinv_0_lt_compat; apply cos_gt_0; assumption.
Qed.

Lemma tan_lt_0 : forall x:R, - (PI / 2) < x -> x < 0 -> tan x < 0.
Proof.
  intros x H1 H2; unfold tan in |- *;
    generalize (cos_gt_0 x H1 (Rlt_trans x 0 (PI / 2) H2 PI2_RGT_0));
      intro H3; rewrite <- Ropp_0;
        replace (sin x / cos x) with (- (- sin x / cos x)).
  rewrite <- sin_neg; apply Ropp_gt_lt_contravar;
    change (0 < sin (- x) / cos x) in |- *; unfold Rdiv in |- *;
      apply Rmult_lt_0_compat.
  apply sin_gt_0.
  rewrite <- Ropp_0; apply Ropp_gt_lt_contravar; assumption.
  apply Rlt_trans with (PI / 2).
  rewrite <- (Ropp_involutive (PI / 2)); apply Ropp_gt_lt_contravar; assumption.
  apply PI2_Rlt_PI.
  apply Rinv_0_lt_compat; assumption.
  unfold Rdiv in |- *; ring.
Qed.

Lemma cos_ge_0_3PI2 :
  forall x:R, 3 * (PI / 2) <= x -> x <= 2 * PI -> 0 <= cos x.
Proof.
  intros; rewrite <- cos_neg; rewrite <- (cos_period (- x) 1);
    unfold INR in |- *; replace (- x + 2 * 1 * PI) with (2 * PI - x).
  generalize (Ropp_le_ge_contravar x (2 * PI) H0); intro H1;
    generalize (Rge_le (- x) (- (2 * PI)) H1); clear H1;
      intro H1; generalize (Rplus_le_compat_l (2 * PI) (- (2 * PI)) (- x) H1).
  rewrite Rplus_opp_r.
  intro H2; generalize (Ropp_le_ge_contravar (3 * (PI / 2)) x H); intro H3;
    generalize (Rge_le (- (3 * (PI / 2))) (- x) H3); clear H3;
      intro H3;
        generalize (Rplus_le_compat_l (2 * PI) (- x) (- (3 * (PI / 2))) H3).
  replace (2 * PI + - (3 * (PI / 2))) with (PI / 2).
  intro H4;
    apply
      (cos_ge_0 (2 * PI - x)
        (Rlt_le (- (PI / 2)) (2 * PI - x)
          (Rlt_le_trans (- (PI / 2)) 0 (2 * PI - x) _PI2_RLT_0 H2)) H4).
  rewrite double; pattern PI at 2 3 in |- *; rewrite double_var; ring.
  ring.
Qed.

Lemma form1 :
  forall p q:R, cos p + cos q = 2 * cos ((p - q) / 2) * cos ((p + q) / 2).
Proof.
  intros p q; pattern p at 1 in |- *;
    replace p with ((p - q) / 2 + (p + q) / 2).
  rewrite <- (cos_neg q); replace (- q) with ((p - q) / 2 - (p + q) / 2).
  rewrite cos_plus; rewrite cos_minus; ring.
  pattern q at 3 in |- *; rewrite double_var; unfold Rdiv in |- *; ring.
  pattern p at 3 in |- *; rewrite double_var; unfold Rdiv in |- *; ring.
Qed.

Lemma form2 :
  forall p q:R, cos p - cos q = -2 * sin ((p - q) / 2) * sin ((p + q) / 2).
Proof.
  intros p q; pattern p at 1 in |- *;
    replace p with ((p - q) / 2 + (p + q) / 2).
  rewrite <- (cos_neg q); replace (- q) with ((p - q) / 2 - (p + q) / 2).
  rewrite cos_plus; rewrite cos_minus; ring.
  pattern q at 3 in |- *; rewrite double_var; unfold Rdiv in |- *; ring.
  pattern p at 3 in |- *; rewrite double_var; unfold Rdiv in |- *; ring.
Qed.

Lemma form3 :
  forall p q:R, sin p + sin q = 2 * cos ((p - q) / 2) * sin ((p + q) / 2).
Proof.
  intros p q; pattern p at 1 in |- *;
    replace p with ((p - q) / 2 + (p + q) / 2).
  pattern q at 3 in |- *; replace q with ((p + q) / 2 - (p - q) / 2).
  rewrite sin_plus; rewrite sin_minus; ring.
  pattern q at 3 in |- *; rewrite double_var; unfold Rdiv in |- *; ring.
  pattern p at 3 in |- *; rewrite double_var; unfold Rdiv in |- *; ring.
Qed.

Lemma form4 :
  forall p q:R, sin p - sin q = 2 * cos ((p + q) / 2) * sin ((p - q) / 2).
Proof.
  intros p q; pattern p at 1 in |- *;
    replace p with ((p - q) / 2 + (p + q) / 2).
  pattern q at 3 in |- *; replace q with ((p + q) / 2 - (p - q) / 2).
  rewrite sin_plus; rewrite sin_minus; ring.
  pattern q at 3 in |- *; rewrite double_var; unfold Rdiv in |- *; ring.
  pattern p at 3 in |- *; rewrite double_var; unfold Rdiv in |- *; ring.

Qed.

Lemma sin_increasing_0 :
  forall x y:R,
    - (PI / 2) <= x ->
    x <= PI / 2 -> - (PI / 2) <= y -> y <= PI / 2 -> sin x < sin y -> x < y.
Proof.
  intros; cut (sin ((x - y) / 2) < 0).
  intro H4; case (Rtotal_order ((x - y) / 2) 0); intro H5.
  assert (Hyp : 0 < 2).
  prove_sup0.
  generalize (Rmult_lt_compat_l 2 ((x - y) / 2) 0 Hyp H5).
  unfold Rdiv in |- *.
  rewrite <- Rmult_assoc.
  rewrite Rinv_r_simpl_m.
  rewrite Rmult_0_r.
  clear H5; intro H5; apply Rminus_lt; assumption.
  discrR.
  elim H5; intro H6.
  rewrite H6 in H4; rewrite sin_0 in H4; elim (Rlt_irrefl 0 H4).
  change (0 < (x - y) / 2) in H6;
    generalize (Ropp_le_ge_contravar (- (PI / 2)) y H1).
  rewrite Ropp_involutive.
  intro H7; generalize (Rge_le (PI / 2) (- y) H7); clear H7; intro H7;
    generalize (Rplus_le_compat x (PI / 2) (- y) (PI / 2) H0 H7).
  rewrite <- double_var.
  intro H8.
  assert (Hyp : 0 < 2).
  prove_sup0.
  generalize
    (Rmult_le_compat_l (/ 2) (x - y) PI
      (Rlt_le 0 (/ 2) (Rinv_0_lt_compat 2 Hyp)) H8).
  repeat rewrite (Rmult_comm (/ 2)).
  intro H9;
    generalize
      (sin_gt_0 ((x - y) / 2) H6
        (Rle_lt_trans ((x - y) / 2) (PI / 2) PI H9 PI2_Rlt_PI));
      intro H10;
        elim
          (Rlt_irrefl (sin ((x - y) / 2))
            (Rlt_trans (sin ((x - y) / 2)) 0 (sin ((x - y) / 2)) H4 H10)).
  generalize (Rlt_minus (sin x) (sin y) H3); clear H3; intro H3;
    rewrite form4 in H3;
      generalize (Rplus_le_compat x (PI / 2) y (PI / 2) H0 H2).
  rewrite <- double_var.
  assert (Hyp : 0 < 2).
  prove_sup0.
  intro H4;
    generalize
      (Rmult_le_compat_l (/ 2) (x + y) PI
        (Rlt_le 0 (/ 2) (Rinv_0_lt_compat 2 Hyp)) H4).
  repeat rewrite (Rmult_comm (/ 2)).
  clear H4; intro H4;
    generalize (Rplus_le_compat (- (PI / 2)) x (- (PI / 2)) y H H1);
      replace (- (PI / 2) + - (PI / 2)) with (- PI).
  intro H5;
    generalize
      (Rmult_le_compat_l (/ 2) (- PI) (x + y)
        (Rlt_le 0 (/ 2) (Rinv_0_lt_compat 2 Hyp)) H5).
  replace (/ 2 * (x + y)) with ((x + y) / 2).
  replace (/ 2 * - PI) with (- (PI / 2)).
  clear H5; intro H5; elim H4; intro H40.
  elim H5; intro H50.
  generalize (cos_gt_0 ((x + y) / 2) H50 H40); intro H6;
    generalize (Rmult_lt_compat_l 2 0 (cos ((x + y) / 2)) Hyp H6).
  rewrite Rmult_0_r.
  clear H6; intro H6; case (Rcase_abs (sin ((x - y) / 2))); intro H7.
  assumption.
  generalize (Rge_le (sin ((x - y) / 2)) 0 H7); clear H7; intro H7;
    generalize
      (Rmult_le_pos (2 * cos ((x + y) / 2)) (sin ((x - y) / 2))
        (Rlt_le 0 (2 * cos ((x + y) / 2)) H6) H7); intro H8;
      generalize
        (Rle_lt_trans 0 (2 * cos ((x + y) / 2) * sin ((x - y) / 2)) 0 H8 H3);
        intro H9; elim (Rlt_irrefl 0 H9).
  rewrite <- H50 in H3; rewrite cos_neg in H3; rewrite cos_PI2 in H3;
    rewrite Rmult_0_r in H3; rewrite Rmult_0_l in H3;
      elim (Rlt_irrefl 0 H3).
  unfold Rdiv in H3.
  rewrite H40 in H3; assert (H50 := cos_PI2); unfold Rdiv in H50;
    rewrite H50 in H3; rewrite Rmult_0_r in H3; rewrite Rmult_0_l in H3;
      elim (Rlt_irrefl 0 H3).
  unfold Rdiv in |- *.
  rewrite <- Ropp_mult_distr_l_reverse.
  apply Rmult_comm.
  unfold Rdiv in |- *; apply Rmult_comm.
  pattern PI at 1 in |- *; rewrite double_var.
  rewrite Ropp_plus_distr.
  reflexivity.
Qed.

Lemma sin_increasing_1 :
  forall x y:R,
    - (PI / 2) <= x ->
    x <= PI / 2 -> - (PI / 2) <= y -> y <= PI / 2 -> x < y -> sin x < sin y.
Proof.
  intros; generalize (Rplus_lt_compat_l x x y H3); intro H4;
    generalize (Rplus_le_compat (- (PI / 2)) x (- (PI / 2)) x H H);
      replace (- (PI / 2) + - (PI / 2)) with (- PI).
  assert (Hyp : 0 < 2).
  prove_sup0.
  intro H5; generalize (Rle_lt_trans (- PI) (x + x) (x + y) H5 H4); intro H6;
    generalize
      (Rmult_lt_compat_l (/ 2) (- PI) (x + y) (Rinv_0_lt_compat 2 Hyp) H6);
      replace (/ 2 * - PI) with (- (PI / 2)).
  replace (/ 2 * (x + y)) with ((x + y) / 2).
  clear H4 H5 H6; intro H4; generalize (Rplus_lt_compat_l y x y H3); intro H5;
    rewrite Rplus_comm in H5;
      generalize (Rplus_le_compat y (PI / 2) y (PI / 2) H2 H2).
  rewrite <- double_var.
  intro H6; generalize (Rlt_le_trans (x + y) (y + y) PI H5 H6); intro H7;
    generalize (Rmult_lt_compat_l (/ 2) (x + y) PI (Rinv_0_lt_compat 2 Hyp) H7);
      replace (/ 2 * PI) with (PI / 2).
  replace (/ 2 * (x + y)) with ((x + y) / 2).
  clear H5 H6 H7; intro H5; generalize (Ropp_le_ge_contravar (- (PI / 2)) y H1);
    rewrite Ropp_involutive; clear H1; intro H1;
      generalize (Rge_le (PI / 2) (- y) H1); clear H1; intro H1;
        generalize (Ropp_le_ge_contravar y (PI / 2) H2); clear H2;
          intro H2; generalize (Rge_le (- y) (- (PI / 2)) H2);
            clear H2; intro H2; generalize (Rplus_lt_compat_l (- y) x y H3);
              replace (- y + x) with (x - y).
  rewrite Rplus_opp_l.
  intro H6;
    generalize (Rmult_lt_compat_l (/ 2) (x - y) 0 (Rinv_0_lt_compat 2 Hyp) H6);
      rewrite Rmult_0_r; replace (/ 2 * (x - y)) with ((x - y) / 2).
  clear H6; intro H6;
    generalize (Rplus_le_compat (- (PI / 2)) x (- (PI / 2)) (- y) H H2);
      replace (- (PI / 2) + - (PI / 2)) with (- PI).
  replace (x + - y) with (x - y).
  intro H7;
    generalize
      (Rmult_le_compat_l (/ 2) (- PI) (x - y)
        (Rlt_le 0 (/ 2) (Rinv_0_lt_compat 2 Hyp)) H7);
      replace (/ 2 * - PI) with (- (PI / 2)).
  replace (/ 2 * (x - y)) with ((x - y) / 2).
  clear H7; intro H7; clear H H0 H1 H2; apply Rminus_lt; rewrite form4;
    generalize (cos_gt_0 ((x + y) / 2) H4 H5); intro H8;
      generalize (Rmult_lt_0_compat 2 (cos ((x + y) / 2)) Hyp H8);
        clear H8; intro H8; cut (- PI < - (PI / 2)).
  intro H9;
    generalize
      (sin_lt_0_var ((x - y) / 2)
        (Rlt_le_trans (- PI) (- (PI / 2)) ((x - y) / 2) H9 H7) H6);
      intro H10;
        generalize
          (Rmult_lt_gt_compat_neg_l (sin ((x - y) / 2)) 0 (
            2 * cos ((x + y) / 2)) H10 H8); intro H11; rewrite Rmult_0_r in H11;
          rewrite Rmult_comm; assumption.
  apply Ropp_lt_gt_contravar; apply PI2_Rlt_PI.
  unfold Rdiv in |- *; apply Rmult_comm.
  unfold Rdiv in |- *; rewrite <- Ropp_mult_distr_l_reverse; apply Rmult_comm.
  reflexivity.
  pattern PI at 1 in |- *; rewrite double_var.
  rewrite Ropp_plus_distr.
  reflexivity.
  unfold Rdiv in |- *; apply Rmult_comm.
  unfold Rminus in |- *; apply Rplus_comm.
  unfold Rdiv in |- *; apply Rmult_comm.
  unfold Rdiv in |- *; apply Rmult_comm.
  unfold Rdiv in |- *; apply Rmult_comm.
  unfold Rdiv in |- *.
  rewrite <- Ropp_mult_distr_l_reverse.
  apply Rmult_comm.
  pattern PI at 1 in |- *; rewrite double_var.
  rewrite Ropp_plus_distr.
  reflexivity.
Qed.

Lemma sin_decreasing_0 :
  forall x y:R,
    x <= 3 * (PI / 2) ->
    PI / 2 <= x -> y <= 3 * (PI / 2) -> PI / 2 <= y -> sin x < sin y -> y < x.
Proof.
  intros; rewrite <- (sin_PI_x x) in H3; rewrite <- (sin_PI_x y) in H3;
    generalize (Ropp_lt_gt_contravar (sin (PI - x)) (sin (PI - y)) H3);
      repeat rewrite <- sin_neg;
        generalize (Rplus_le_compat_l (- PI) x (3 * (PI / 2)) H);
          generalize (Rplus_le_compat_l (- PI) (PI / 2) x H0);
            generalize (Rplus_le_compat_l (- PI) y (3 * (PI / 2)) H1);
              generalize (Rplus_le_compat_l (- PI) (PI / 2) y H2);
                replace (- PI + x) with (x - PI).
  replace (- PI + PI / 2) with (- (PI / 2)).
  replace (- PI + y) with (y - PI).
  replace (- PI + 3 * (PI / 2)) with (PI / 2).
  replace (- (PI - x)) with (x - PI).
  replace (- (PI - y)) with (y - PI).
  intros; change (sin (y - PI) < sin (x - PI)) in H8;
    apply Rplus_lt_reg_r with (- PI); rewrite Rplus_comm;
      replace (y + - PI) with (y - PI).
  rewrite Rplus_comm; replace (x + - PI) with (x - PI).
  apply (sin_increasing_0 (y - PI) (x - PI) H4 H5 H6 H7 H8).
  reflexivity.
  reflexivity.
  unfold Rminus in |- *; rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  apply Rplus_comm.
  unfold Rminus in |- *; rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  apply Rplus_comm.
  pattern PI at 2 in |- *; rewrite double_var.
  rewrite Ropp_plus_distr.
  ring.
  unfold Rminus in |- *; apply Rplus_comm.
  pattern PI at 2 in |- *; rewrite double_var.
  rewrite Ropp_plus_distr.
  ring.
  unfold Rminus in |- *; apply Rplus_comm.
Qed.

Lemma sin_decreasing_1 :
  forall x y:R,
    x <= 3 * (PI / 2) ->
    PI / 2 <= x -> y <= 3 * (PI / 2) -> PI / 2 <= y -> x < y -> sin y < sin x.
Proof.
  intros; rewrite <- (sin_PI_x x); rewrite <- (sin_PI_x y);
    generalize (Rplus_le_compat_l (- PI) x (3 * (PI / 2)) H);
      generalize (Rplus_le_compat_l (- PI) (PI / 2) x H0);
        generalize (Rplus_le_compat_l (- PI) y (3 * (PI / 2)) H1);
          generalize (Rplus_le_compat_l (- PI) (PI / 2) y H2);
            generalize (Rplus_lt_compat_l (- PI) x y H3);
              replace (- PI + PI / 2) with (- (PI / 2)).
  replace (- PI + y) with (y - PI).
  replace (- PI + 3 * (PI / 2)) with (PI / 2).
  replace (- PI + x) with (x - PI).
  intros; apply Ropp_lt_cancel; repeat rewrite <- sin_neg;
    replace (- (PI - x)) with (x - PI).
  replace (- (PI - y)) with (y - PI).
  apply (sin_increasing_1 (x - PI) (y - PI) H7 H8 H5 H6 H4).
  unfold Rminus in |- *; rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  apply Rplus_comm.
  unfold Rminus in |- *; rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  apply Rplus_comm.
  unfold Rminus in |- *; apply Rplus_comm.
  pattern PI at 2 in |- *; rewrite double_var; ring.
  unfold Rminus in |- *; apply Rplus_comm.
  pattern PI at 2 in |- *; rewrite double_var; ring.
Qed.

Lemma cos_increasing_0 :
  forall x y:R,
    PI <= x -> x <= 2 * PI -> PI <= y -> y <= 2 * PI -> cos x < cos y -> x < y.
Proof.
  intros x y H1 H2 H3 H4; rewrite <- (cos_neg x); rewrite <- (cos_neg y);
    rewrite <- (cos_period (- x) 1); rewrite <- (cos_period (- y) 1);
      unfold INR in |- *;
        replace (- x + 2 * 1 * PI) with (PI / 2 - (x - 3 * (PI / 2))).
  replace (- y + 2 * 1 * PI) with (PI / 2 - (y - 3 * (PI / 2))).
  repeat rewrite cos_shift; intro H5;
    generalize (Rplus_le_compat_l (-3 * (PI / 2)) PI x H1);
      generalize (Rplus_le_compat_l (-3 * (PI / 2)) x (2 * PI) H2);
        generalize (Rplus_le_compat_l (-3 * (PI / 2)) PI y H3);
          generalize (Rplus_le_compat_l (-3 * (PI / 2)) y (2 * PI) H4).
  replace (-3 * (PI / 2) + y) with (y - 3 * (PI / 2)).
  replace (-3 * (PI / 2) + x) with (x - 3 * (PI / 2)).
  replace (-3 * (PI / 2) + 2 * PI) with (PI / 2).
  replace (-3 * (PI / 2) + PI) with (- (PI / 2)).
  clear H1 H2 H3 H4; intros H1 H2 H3 H4;
    apply Rplus_lt_reg_r with (-3 * (PI / 2));
      replace (-3 * (PI / 2) + x) with (x - 3 * (PI / 2)).
  replace (-3 * (PI / 2) + y) with (y - 3 * (PI / 2)).
  apply (sin_increasing_0 (x - 3 * (PI / 2)) (y - 3 * (PI / 2)) H4 H3 H2 H1 H5).
  unfold Rminus in |- *.
  rewrite Ropp_mult_distr_l_reverse.
  apply Rplus_comm.
  unfold Rminus in |- *.
  rewrite Ropp_mult_distr_l_reverse.
  apply Rplus_comm.
  pattern PI at 3 in |- *; rewrite double_var.
  ring.
  rewrite double; pattern PI at 3 4 in |- *; rewrite double_var.
  ring.
  unfold Rminus in |- *.
  rewrite Ropp_mult_distr_l_reverse.
  apply Rplus_comm.
  unfold Rminus in |- *.
  rewrite Ropp_mult_distr_l_reverse.
  apply Rplus_comm.
  rewrite Rmult_1_r.
  rewrite (double PI); pattern PI at 3 4 in |- *; rewrite double_var.
  ring.
  rewrite Rmult_1_r.
  rewrite (double PI); pattern PI at 3 4 in |- *; rewrite double_var.
  ring.
Qed.

Lemma cos_increasing_1 :
  forall x y:R,
    PI <= x -> x <= 2 * PI -> PI <= y -> y <= 2 * PI -> x < y -> cos x < cos y.
Proof.
  intros x y H1 H2 H3 H4 H5;
    generalize (Rplus_le_compat_l (-3 * (PI / 2)) PI x H1);
      generalize (Rplus_le_compat_l (-3 * (PI / 2)) x (2 * PI) H2);
        generalize (Rplus_le_compat_l (-3 * (PI / 2)) PI y H3);
          generalize (Rplus_le_compat_l (-3 * (PI / 2)) y (2 * PI) H4);
            generalize (Rplus_lt_compat_l (-3 * (PI / 2)) x y H5);
              rewrite <- (cos_neg x); rewrite <- (cos_neg y);
                rewrite <- (cos_period (- x) 1); rewrite <- (cos_period (- y) 1);
                  unfold INR in |- *; replace (-3 * (PI / 2) + x) with (x - 3 * (PI / 2)).
  replace (-3 * (PI / 2) + y) with (y - 3 * (PI / 2)).
  replace (-3 * (PI / 2) + PI) with (- (PI / 2)).
  replace (-3 * (PI / 2) + 2 * PI) with (PI / 2).
  clear H1 H2 H3 H4 H5; intros H1 H2 H3 H4 H5;
    replace (- x + 2 * 1 * PI) with (PI / 2 - (x - 3 * (PI / 2))).
  replace (- y + 2 * 1 * PI) with (PI / 2 - (y - 3 * (PI / 2))).
  repeat rewrite cos_shift;
    apply
      (sin_increasing_1 (x - 3 * (PI / 2)) (y - 3 * (PI / 2)) H5 H4 H3 H2 H1).
  rewrite Rmult_1_r.
  rewrite (double PI); pattern PI at 3 4 in |- *; rewrite double_var.
  ring.
  rewrite Rmult_1_r.
  rewrite (double PI); pattern PI at 3 4 in |- *; rewrite double_var.
  ring.
  rewrite (double PI); pattern PI at 3 4 in |- *; rewrite double_var.
  ring.
  pattern PI at 3 in |- *; rewrite double_var; ring.
  unfold Rminus in |- *.
  rewrite <- Ropp_mult_distr_l_reverse.
  apply Rplus_comm.
  unfold Rminus in |- *.
  rewrite <- Ropp_mult_distr_l_reverse.
  apply Rplus_comm.
Qed.

Lemma cos_decreasing_0 :
  forall x y:R,
    0 <= x -> x <= PI -> 0 <= y -> y <= PI -> cos x < cos y -> y < x.
Proof.
  intros; generalize (Ropp_lt_gt_contravar (cos x) (cos y) H3);
    repeat rewrite <- neg_cos; intro H4;
      change (cos (y + PI) < cos (x + PI)) in H4; rewrite (Rplus_comm x) in H4;
        rewrite (Rplus_comm y) in H4; generalize (Rplus_le_compat_l PI 0 x H);
          generalize (Rplus_le_compat_l PI x PI H0);
            generalize (Rplus_le_compat_l PI 0 y H1);
              generalize (Rplus_le_compat_l PI y PI H2); rewrite Rplus_0_r.
  rewrite <- double.
  clear H H0 H1 H2 H3; intros; apply Rplus_lt_reg_r with PI;
    apply (cos_increasing_0 (PI + y) (PI + x) H0 H H2 H1 H4).
Qed.

Lemma cos_decreasing_1 :
  forall x y:R,
    0 <= x -> x <= PI -> 0 <= y -> y <= PI -> x < y -> cos y < cos x.
Proof.
  intros; apply Ropp_lt_cancel; repeat rewrite <- neg_cos;
    rewrite (Rplus_comm x); rewrite (Rplus_comm y);
      generalize (Rplus_le_compat_l PI 0 x H);
        generalize (Rplus_le_compat_l PI x PI H0);
          generalize (Rplus_le_compat_l PI 0 y H1);
            generalize (Rplus_le_compat_l PI y PI H2); rewrite Rplus_0_r.
  rewrite <- double.
  generalize (Rplus_lt_compat_l PI x y H3); clear H H0 H1 H2 H3; intros;
    apply (cos_increasing_1 (PI + x) (PI + y) H3 H2 H1 H0 H).
Qed.

Lemma tan_diff :
  forall x y:R,
    cos x <> 0 -> cos y <> 0 -> tan x - tan y = sin (x - y) / (cos x * cos y).
Proof.
  intros; unfold tan in |- *; rewrite sin_minus.
  unfold Rdiv in |- *.
  unfold Rminus in |- *.
  rewrite Rmult_plus_distr_r.
  rewrite Rinv_mult_distr.
  repeat rewrite (Rmult_comm (sin x)).
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (cos y)).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm (sin x)).
  apply Rplus_eq_compat_l.
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite <- Ropp_mult_distr_r_reverse.
  rewrite (Rmult_comm (/ cos x)).
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (cos x)).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma tan_increasing_0 :
  forall x y:R,
    - (PI / 4) <= x ->
    x <= PI / 4 -> - (PI / 4) <= y -> y <= PI / 4 -> tan x < tan y -> x < y.
Proof.
  intros; generalize PI4_RLT_PI2; intro H4;
    generalize (Ropp_lt_gt_contravar (PI / 4) (PI / 2) H4);
      intro H5; change (- (PI / 2) < - (PI / 4)) in H5;
        generalize
          (cos_gt_0 x (Rlt_le_trans (- (PI / 2)) (- (PI / 4)) x H5 H)
            (Rle_lt_trans x (PI / 4) (PI / 2) H0 H4)); intro HP1;
          generalize
            (cos_gt_0 y (Rlt_le_trans (- (PI / 2)) (- (PI / 4)) y H5 H1)
              (Rle_lt_trans y (PI / 4) (PI / 2) H2 H4)); intro HP2;
            generalize
              (sym_not_eq
                (Rlt_not_eq 0 (cos x)
                  (cos_gt_0 x (Rlt_le_trans (- (PI / 2)) (- (PI / 4)) x H5 H)
                    (Rle_lt_trans x (PI / 4) (PI / 2) H0 H4))));
              intro H6;
                generalize
                  (sym_not_eq
                    (Rlt_not_eq 0 (cos y)
                      (cos_gt_0 y (Rlt_le_trans (- (PI / 2)) (- (PI / 4)) y H5 H1)
                        (Rle_lt_trans y (PI / 4) (PI / 2) H2 H4))));
                  intro H7; generalize (tan_diff x y H6 H7); intro H8;
                    generalize (Rlt_minus (tan x) (tan y) H3); clear H3;
                      intro H3; rewrite H8 in H3; cut (sin (x - y) < 0).
  intro H9; generalize (Ropp_le_ge_contravar (- (PI / 4)) y H1);
    rewrite Ropp_involutive; intro H10; generalize (Rge_le (PI / 4) (- y) H10);
      clear H10; intro H10; generalize (Ropp_le_ge_contravar y (PI / 4) H2);
        intro H11; generalize (Rge_le (- y) (- (PI / 4)) H11);
          clear H11; intro H11;
            generalize (Rplus_le_compat (- (PI / 4)) x (- (PI / 4)) (- y) H H11);
              generalize (Rplus_le_compat x (PI / 4) (- y) (PI / 4) H0 H10);
                replace (x + - y) with (x - y).
  replace (PI / 4 + PI / 4) with (PI / 2).
  replace (- (PI / 4) + - (PI / 4)) with (- (PI / 2)).
  intros; case (Rtotal_order 0 (x - y)); intro H14.
  generalize
    (sin_gt_0 (x - y) H14 (Rle_lt_trans (x - y) (PI / 2) PI H12 PI2_Rlt_PI));
    intro H15; elim (Rlt_irrefl 0 (Rlt_trans 0 (sin (x - y)) 0 H15 H9)).
  elim H14; intro H15.
  rewrite <- H15 in H9; rewrite sin_0 in H9; elim (Rlt_irrefl 0 H9).
  apply Rminus_lt; assumption.
  pattern PI at 1 in |- *; rewrite double_var.
  unfold Rdiv in |- *.
  rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_mult_distr.
  rewrite Ropp_plus_distr.
  replace 4 with 4.
  reflexivity.
  ring.
  discrR.
  discrR.
  pattern PI at 1 in |- *; rewrite double_var.
  unfold Rdiv in |- *.
  rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_mult_distr.
  replace 4 with 4.
  reflexivity.
  ring.
  discrR.
  discrR.
  reflexivity.
  case (Rcase_abs (sin (x - y))); intro H9.
  assumption.
  generalize (Rge_le (sin (x - y)) 0 H9); clear H9; intro H9;
    generalize (Rinv_0_lt_compat (cos x) HP1); intro H10;
      generalize (Rinv_0_lt_compat (cos y) HP2); intro H11;
        generalize (Rmult_lt_0_compat (/ cos x) (/ cos y) H10 H11);
          replace (/ cos x * / cos y) with (/ (cos x * cos y)).
  intro H12;
    generalize
      (Rmult_le_pos (sin (x - y)) (/ (cos x * cos y)) H9
        (Rlt_le 0 (/ (cos x * cos y)) H12)); intro H13;
      elim
        (Rlt_irrefl 0 (Rle_lt_trans 0 (sin (x - y) * / (cos x * cos y)) 0 H13 H3)).
  rewrite Rinv_mult_distr.
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma tan_increasing_1 :
  forall x y:R,
    - (PI / 4) <= x ->
    x <= PI / 4 -> - (PI / 4) <= y -> y <= PI / 4 -> x < y -> tan x < tan y.
Proof.
  intros; apply Rminus_lt; generalize PI4_RLT_PI2; intro H4;
    generalize (Ropp_lt_gt_contravar (PI / 4) (PI / 2) H4);
      intro H5; change (- (PI / 2) < - (PI / 4)) in H5;
        generalize
          (cos_gt_0 x (Rlt_le_trans (- (PI / 2)) (- (PI / 4)) x H5 H)
            (Rle_lt_trans x (PI / 4) (PI / 2) H0 H4)); intro HP1;
          generalize
            (cos_gt_0 y (Rlt_le_trans (- (PI / 2)) (- (PI / 4)) y H5 H1)
              (Rle_lt_trans y (PI / 4) (PI / 2) H2 H4)); intro HP2;
            generalize
              (sym_not_eq
                (Rlt_not_eq 0 (cos x)
                  (cos_gt_0 x (Rlt_le_trans (- (PI / 2)) (- (PI / 4)) x H5 H)
                    (Rle_lt_trans x (PI / 4) (PI / 2) H0 H4))));
              intro H6;
                generalize
                  (sym_not_eq
                    (Rlt_not_eq 0 (cos y)
                      (cos_gt_0 y (Rlt_le_trans (- (PI / 2)) (- (PI / 4)) y H5 H1)
                        (Rle_lt_trans y (PI / 4) (PI / 2) H2 H4))));
                  intro H7; rewrite (tan_diff x y H6 H7);
                    generalize (Rinv_0_lt_compat (cos x) HP1); intro H10;
                      generalize (Rinv_0_lt_compat (cos y) HP2); intro H11;
                        generalize (Rmult_lt_0_compat (/ cos x) (/ cos y) H10 H11);
                          replace (/ cos x * / cos y) with (/ (cos x * cos y)).
  clear H10 H11; intro H8; generalize (Ropp_le_ge_contravar y (PI / 4) H2);
    intro H11; generalize (Rge_le (- y) (- (PI / 4)) H11);
      clear H11; intro H11;
        generalize (Rplus_le_compat (- (PI / 4)) x (- (PI / 4)) (- y) H H11);
          replace (x + - y) with (x - y).
  replace (- (PI / 4) + - (PI / 4)) with (- (PI / 2)).
  clear H11; intro H9; generalize (Rlt_minus x y H3); clear H3; intro H3;
    clear H H0 H1 H2 H4 H5 HP1 HP2; generalize PI2_Rlt_PI;
      intro H1; generalize (Ropp_lt_gt_contravar (PI / 2) PI H1);
        clear H1; intro H1;
          generalize
            (sin_lt_0_var (x - y) (Rlt_le_trans (- PI) (- (PI / 2)) (x - y) H1 H9) H3);
            intro H2;
              generalize
                (Rmult_lt_gt_compat_neg_l (sin (x - y)) 0 (/ (cos x * cos y)) H2 H8);
                rewrite Rmult_0_r; intro H4; assumption.
  pattern PI at 1 in |- *; rewrite double_var.
  unfold Rdiv in |- *.
  rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_mult_distr.
  replace 4 with 4.
  rewrite Ropp_plus_distr.
  reflexivity.
  ring.
  discrR.
  discrR.
  reflexivity.
  apply Rinv_mult_distr; assumption.
Qed.

Lemma sin_incr_0 :
  forall x y:R,
    - (PI / 2) <= x ->
    x <= PI / 2 -> - (PI / 2) <= y -> y <= PI / 2 -> sin x <= sin y -> x <= y.
Proof.
  intros; case (Rtotal_order (sin x) (sin y)); intro H4;
    [ left; apply (sin_increasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (sin_increasing_1 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl (sin y) H8) ] ]
          | elim (Rlt_irrefl (sin x) (Rle_lt_trans (sin x) (sin y) (sin x) H3 H5)) ] ].
Qed.

Lemma sin_incr_1 :
  forall x y:R,
    - (PI / 2) <= x ->
    x <= PI / 2 -> - (PI / 2) <= y -> y <= PI / 2 -> x <= y -> sin x <= sin y.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (sin_increasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (sin x) (sin y)); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (sin_increasing_0 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl y H8) ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

Lemma sin_decr_0 :
  forall x y:R,
    x <= 3 * (PI / 2) ->
    PI / 2 <= x ->
    y <= 3 * (PI / 2) -> PI / 2 <= y -> sin x <= sin y -> y <= x.
Proof.
  intros; case (Rtotal_order (sin x) (sin y)); intro H4;
    [ left; apply (sin_decreasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ generalize (sin_decreasing_1 x y H H0 H1 H2 H6); intro H8;
            rewrite H5 in H8; elim (Rlt_irrefl (sin y) H8)
            | elim H6; intro H7;
              [ right; symmetry  in |- *; assumption | left; assumption ] ]
          | elim (Rlt_irrefl (sin x) (Rle_lt_trans (sin x) (sin y) (sin x) H3 H5)) ] ].
Qed.

Lemma sin_decr_1 :
  forall x y:R,
    x <= 3 * (PI / 2) ->
    PI / 2 <= x ->
    y <= 3 * (PI / 2) -> PI / 2 <= y -> x <= y -> sin y <= sin x.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (sin_decreasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (sin x) (sin y)); intro H6;
          [ generalize (sin_decreasing_0 x y H H0 H1 H2 H6); intro H8;
            rewrite H5 in H8; elim (Rlt_irrefl y H8)
            | elim H6; intro H7;
              [ right; symmetry  in |- *; assumption | left; assumption ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

Lemma cos_incr_0 :
  forall x y:R,
    PI <= x ->
    x <= 2 * PI -> PI <= y -> y <= 2 * PI -> cos x <= cos y -> x <= y.
Proof.
  intros; case (Rtotal_order (cos x) (cos y)); intro H4;
    [ left; apply (cos_increasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (cos_increasing_1 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl (cos y) H8) ] ]
          | elim (Rlt_irrefl (cos x) (Rle_lt_trans (cos x) (cos y) (cos x) H3 H5)) ] ].
Qed.

Lemma cos_incr_1 :
  forall x y:R,
    PI <= x ->
    x <= 2 * PI -> PI <= y -> y <= 2 * PI -> x <= y -> cos x <= cos y.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (cos_increasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (cos x) (cos y)); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (cos_increasing_0 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl y H8) ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

Lemma cos_decr_0 :
  forall x y:R,
    0 <= x -> x <= PI -> 0 <= y -> y <= PI -> cos x <= cos y -> y <= x.
Proof.
  intros; case (Rtotal_order (cos x) (cos y)); intro H4;
    [ left; apply (cos_decreasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ generalize (cos_decreasing_1 x y H H0 H1 H2 H6); intro H8;
            rewrite H5 in H8; elim (Rlt_irrefl (cos y) H8)
            | elim H6; intro H7;
              [ right; symmetry  in |- *; assumption | left; assumption ] ]
          | elim (Rlt_irrefl (cos x) (Rle_lt_trans (cos x) (cos y) (cos x) H3 H5)) ] ].
Qed.

Lemma cos_decr_1 :
  forall x y:R,
    0 <= x -> x <= PI -> 0 <= y -> y <= PI -> x <= y -> cos y <= cos x.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (cos_decreasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (cos x) (cos y)); intro H6;
          [ generalize (cos_decreasing_0 x y H H0 H1 H2 H6); intro H8;
            rewrite H5 in H8; elim (Rlt_irrefl y H8)
            | elim H6; intro H7;
              [ right; symmetry  in |- *; assumption | left; assumption ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

Lemma tan_incr_0 :
  forall x y:R,
    - (PI / 4) <= x ->
    x <= PI / 4 -> - (PI / 4) <= y -> y <= PI / 4 -> tan x <= tan y -> x <= y.
Proof.
  intros; case (Rtotal_order (tan x) (tan y)); intro H4;
    [ left; apply (tan_increasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (tan_increasing_1 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl (tan y) H8) ] ]
          | elim (Rlt_irrefl (tan x) (Rle_lt_trans (tan x) (tan y) (tan x) H3 H5)) ] ].
Qed.

Lemma tan_incr_1 :
  forall x y:R,
    - (PI / 4) <= x ->
    x <= PI / 4 -> - (PI / 4) <= y -> y <= PI / 4 -> x <= y -> tan x <= tan y.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (tan_increasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (tan x) (tan y)); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (tan_increasing_0 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl y H8) ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

(**********)
Lemma sin_eq_0_1 : forall x:R, (exists k : Z, x = IZR k * PI) -> sin x = 0.
Proof.
  intros.
  elim H; intros.
  apply (Zcase_sign x0).
  intro.
  rewrite H1 in H0.
  simpl in H0.
  rewrite H0; rewrite Rmult_0_l; apply sin_0.
  intro.
  cut (0 <= x0)%Z.
  intro.
  elim (IZN x0 H2); intros.
  rewrite H3 in H0.
  rewrite <- INR_IZR_INZ in H0.
  rewrite H0.
  elim (even_odd_cor x1); intros.
  elim H4; intro.
  rewrite H5.
  rewrite mult_INR.
  simpl in |- *.
  rewrite <- (Rplus_0_l (2 * INR x2 * PI)).
  rewrite sin_period.
  apply sin_0.
  rewrite H5.
  rewrite S_INR; rewrite mult_INR.
  simpl in |- *.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l; rewrite sin_plus.
  rewrite sin_PI.
  rewrite Rmult_0_r.
  rewrite <- (Rplus_0_l (2 * INR x2 * PI)).
  rewrite sin_period.
  rewrite sin_0; ring.
  apply le_IZR.
  left; apply IZR_lt.
  assert (H2 := Zorder.Zgt_iff_lt).
  elim (H2 x0 0%Z); intros.
  apply H3; assumption.
  intro.
  rewrite H0.
  replace (sin (IZR x0 * PI)) with (- sin (- IZR x0 * PI)).
  cut (0 <= - x0)%Z.
  intro.
  rewrite <- Ropp_Ropp_IZR.
  elim (IZN (- x0) H2); intros.
  rewrite H3.
  rewrite <- INR_IZR_INZ.
  elim (even_odd_cor x1); intros.
  elim H4; intro.
  rewrite H5.
  rewrite mult_INR.
  simpl in |- *.
  rewrite <- (Rplus_0_l (2 * INR x2 * PI)).
  rewrite sin_period.
  rewrite sin_0; ring.
  rewrite H5.
  rewrite S_INR; rewrite mult_INR.
  simpl in |- *.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l; rewrite sin_plus.
  rewrite sin_PI.
  rewrite Rmult_0_r.
  rewrite <- (Rplus_0_l (2 * INR x2 * PI)).
  rewrite sin_period.
  rewrite sin_0; ring.
  apply le_IZR.
  apply Rplus_le_reg_l with (IZR x0).
  rewrite Rplus_0_r.
  rewrite Ropp_Ropp_IZR.
  rewrite Rplus_opp_r.
  left; replace 0 with (IZR 0); [ apply IZR_lt | reflexivity ].
  assumption.
  rewrite <- sin_neg.
  rewrite Ropp_mult_distr_l_reverse.
  rewrite Ropp_involutive.
  reflexivity.
Qed.

Lemma sin_eq_0_0 : forall x:R, sin x = 0 ->  exists k : Z, x = IZR k * PI.
Proof.
  intros.
  assert (H0 := euclidian_division x PI PI_neq0).
  elim H0; intros q H1.
  elim H1; intros r H2.
  exists q.
  cut (r = 0).
  intro.
  elim H2; intros H4 _; rewrite H4; rewrite H3.
  apply Rplus_0_r.
  elim H2; intros.
  rewrite H3 in H.
  rewrite sin_plus in H.
  cut (sin (IZR q * PI) = 0).
  intro.
  rewrite H5 in H.
  rewrite Rmult_0_l in H.
  rewrite Rplus_0_l in H.
  assert (H6 := Rmult_integral _ _ H).
  elim H6; intro.
  assert (H8 := sin2_cos2 (IZR q * PI)).
  rewrite H5 in H8; rewrite H7 in H8.
  rewrite Rsqr_0 in H8.
  rewrite Rplus_0_r in H8.
  elim R1_neq_R0; symmetry  in |- *; assumption.
  cut (r = 0 \/ 0 < r < PI).
  intro; elim H8; intro.
  assumption.
  elim H9; intros.
  assert (H12 := sin_gt_0 _ H10 H11).
  rewrite H7 in H12; elim (Rlt_irrefl _ H12).
  rewrite Rabs_right in H4.
  elim H4; intros.
  case (Rtotal_order 0 r); intro.
  right; split; assumption.
  elim H10; intro.
  left; symmetry  in |- *; assumption.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H8 H11)).
  apply Rle_ge.
  left; apply PI_RGT_0.
  apply sin_eq_0_1.
  exists q; reflexivity.
Qed.

Lemma cos_eq_0_0 :
  forall x:R, cos x = 0 ->  exists k : Z, x = IZR k * PI + PI / 2.
Proof.
  intros x H; rewrite cos_sin in H; generalize (sin_eq_0_0 (PI / INR 2 + x) H);
    intro H2; elim H2; intros x0 H3; exists (x0 - Z_of_nat 1)%Z;
      rewrite <- Z_R_minus; simpl.
unfold INR in H3. field_simplify [(sym_eq H3)]. field.
(**
  ring_simplify.
 (* rewrite (Rmult_comm PI);*) (* old ring compat *)
        rewrite <- H3; simpl;
          field;repeat split; discrR.
*)
Qed.

Lemma cos_eq_0_1 :
  forall x:R, (exists k : Z, x = IZR k * PI + PI / 2) -> cos x = 0.
Proof.
  intros x H1; rewrite cos_sin; elim H1; intros x0 H2; rewrite H2;
    replace (PI / 2 + (IZR x0 * PI + PI / 2)) with (IZR x0 * PI + PI).
  rewrite neg_sin; rewrite <- Ropp_0.
  apply Ropp_eq_compat; apply sin_eq_0_1; exists x0; reflexivity.
  pattern PI at 2 in |- *; rewrite (double_var PI); ring.
Qed.

Lemma sin_eq_O_2PI_0 :
  forall x:R,
    0 <= x -> x <= 2 * PI -> sin x = 0 -> x = 0 \/ x = PI \/ x = 2 * PI.
Proof.
  intros; generalize (sin_eq_0_0 x H1); intro.
  elim H2; intros k0 H3.
  case (Rtotal_order PI x); intro.
  rewrite H3 in H4; rewrite H3 in H0.
  right; right.
  generalize
    (Rmult_lt_compat_r (/ PI) PI (IZR k0 * PI) (Rinv_0_lt_compat PI PI_RGT_0) H4);
    rewrite Rmult_assoc; repeat rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; intro;
    generalize
      (Rmult_le_compat_r (/ PI) (IZR k0 * PI) (2 * PI)
        (Rlt_le 0 (/ PI) (Rinv_0_lt_compat PI PI_RGT_0)) H0);
      repeat rewrite Rmult_assoc; repeat rewrite <- Rinv_r_sym.
  repeat rewrite Rmult_1_r; intro;
    generalize (Rplus_lt_compat_l (IZR (-2)) 1 (IZR k0) H5);
      rewrite <- plus_IZR.
  replace (IZR (-2) + 1) with (-1).
  intro; generalize (Rplus_le_compat_l (IZR (-2)) (IZR k0) 2 H6);
    rewrite <- plus_IZR.
  replace (IZR (-2) + 2) with 0.
  intro; cut (-1 < IZR (-2 + k0) < 1).
  intro; generalize (one_IZR_lt1 (-2 + k0) H9); intro.
  cut (k0 = 2%Z).
  intro; rewrite H11 in H3; rewrite H3; simpl in |- *.
  reflexivity.
  rewrite <- (Zplus_opp_l 2) in H10; generalize (Zplus_reg_l (-2) k0 2 H10);
    intro; assumption.
  split.
  assumption.
  apply Rle_lt_trans with 0.
  assumption.
  apply Rlt_0_1.
  simpl in |- *; ring.
  simpl in |- *; ring.
  apply PI_neq0.
  apply PI_neq0.
  elim H4; intro.
  right; left.
  symmetry  in |- *; assumption.
  left.
  rewrite H3 in H5; rewrite H3 in H;
    generalize
      (Rmult_lt_compat_r (/ PI) (IZR k0 * PI) PI (Rinv_0_lt_compat PI PI_RGT_0)
        H5); rewrite Rmult_assoc; repeat rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; intro;
    generalize
      (Rmult_le_compat_r (/ PI) 0 (IZR k0 * PI)
        (Rlt_le 0 (/ PI) (Rinv_0_lt_compat PI PI_RGT_0)) H);
      repeat rewrite Rmult_assoc; repeat rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; rewrite Rmult_0_l; intro.
  cut (-1 < IZR k0 < 1).
  intro; generalize (one_IZR_lt1 k0 H8); intro; rewrite H9 in H3; rewrite H3;
    simpl in |- *; apply Rmult_0_l.
  split.
  apply Rlt_le_trans with 0.
  rewrite <- Ropp_0; apply Ropp_gt_lt_contravar; apply Rlt_0_1.
  assumption.
  assumption.
  apply PI_neq0.
  apply PI_neq0.
Qed.

Lemma sin_eq_O_2PI_1 :
  forall x:R,
    0 <= x -> x <= 2 * PI -> x = 0 \/ x = PI \/ x = 2 * PI -> sin x = 0.
Proof.
  intros x H1 H2 H3; elim H3; intro H4;
    [ rewrite H4; rewrite sin_0; reflexivity
      | elim H4; intro H5;
        [ rewrite H5; rewrite sin_PI; reflexivity
          | rewrite H5; rewrite sin_2PI; reflexivity ] ].
Qed.

Lemma cos_eq_0_2PI_0 :
  forall x:R,
    0 <= x -> x <= 2 * PI -> cos x = 0 -> x = PI / 2 \/ x = 3 * (PI / 2).
Proof.
  intros; case (Rtotal_order x (3 * (PI / 2))); intro.
  rewrite cos_sin in H1.
  cut (0 <= PI / 2 + x).
  cut (PI / 2 + x <= 2 * PI).
  intros; generalize (sin_eq_O_2PI_0 (PI / 2 + x) H4 H3 H1); intros.
  decompose [or] H5.
  generalize (Rplus_le_compat_l (PI / 2) 0 x H); rewrite Rplus_0_r; rewrite H6;
    intro.
  elim (Rlt_irrefl 0 (Rlt_le_trans 0 (PI / 2) 0 PI2_RGT_0 H7)).
  left.
  generalize (Rplus_eq_compat_l (- (PI / 2)) (PI / 2 + x) PI H7).
  replace (- (PI / 2) + (PI / 2 + x)) with x.
  replace (- (PI / 2) + PI) with (PI / 2).
  intro; assumption.
  pattern PI at 3 in |- *; rewrite (double_var PI); ring.
  ring.
  right.
  generalize (Rplus_eq_compat_l (- (PI / 2)) (PI / 2 + x) (2 * PI) H7).
  replace (- (PI / 2) + (PI / 2 + x)) with x.
  replace (- (PI / 2) + 2 * PI) with (3 * (PI / 2)).
  intro; assumption.
  rewrite double; pattern PI at 3 4 in |- *; rewrite (double_var PI); ring.
  ring.
  left; replace (2 * PI) with (PI / 2 + 3 * (PI / 2)).
  apply Rplus_lt_compat_l; assumption.
  rewrite (double PI); pattern PI at 3 4 in |- *; rewrite (double_var PI); ring.
  apply Rplus_le_le_0_compat.
  left; unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  apply PI_RGT_0.
  apply Rinv_0_lt_compat; prove_sup0.
  assumption.
  elim H2; intro.
  right; assumption.
  generalize (cos_eq_0_0 x H1); intro; elim H4; intros k0 H5.
  rewrite H5 in H3; rewrite H5 in H0;
    generalize
      (Rplus_lt_compat_l (- (PI / 2)) (3 * (PI / 2)) (IZR k0 * PI + PI / 2) H3);
      generalize
        (Rplus_le_compat_l (- (PI / 2)) (IZR k0 * PI + PI / 2) (2 * PI) H0).
  replace (- (PI / 2) + 3 * (PI / 2)) with PI.
  replace (- (PI / 2) + (IZR k0 * PI + PI / 2)) with (IZR k0 * PI).
  replace (- (PI / 2) + 2 * PI) with (3 * (PI / 2)).
  intros;
    generalize
      (Rmult_lt_compat_l (/ PI) PI (IZR k0 * PI) (Rinv_0_lt_compat PI PI_RGT_0)
        H7);
      generalize
        (Rmult_le_compat_l (/ PI) (IZR k0 * PI) (3 * (PI / 2))
          (Rlt_le 0 (/ PI) (Rinv_0_lt_compat PI PI_RGT_0)) H6).
  replace (/ PI * (IZR k0 * PI)) with (IZR k0).
  replace (/ PI * (3 * (PI / 2))) with (3 * / 2).
  rewrite <- Rinv_l_sym.
  intros; generalize (Rplus_lt_compat_l (IZR (-2)) 1 (IZR k0) H9);
    rewrite <- plus_IZR.
  replace (IZR (-2) + 1) with (-1).
  intro; generalize (Rplus_le_compat_l (IZR (-2)) (IZR k0) (3 * / 2) H8);
    rewrite <- plus_IZR.
  replace (IZR (-2) + 2) with 0.
  intro; cut (-1 < IZR (-2 + k0) < 1).
  intro; generalize (one_IZR_lt1 (-2 + k0) H12); intro.
  cut (k0 = 2%Z).
  intro; rewrite H14 in H8.
  assert (Hyp : 0 < 2).
  prove_sup0.
  generalize (Rmult_le_compat_l 2 (IZR 2) (3 * / 2) (Rlt_le 0 2 Hyp) H8);
    simpl in |- *.
  replace 4 with 4.
  replace (2 * (3 * / 2)) with 3.
  intro; cut (3 < 4).
  intro; elim (Rlt_irrefl 3 (Rlt_le_trans 3 4 3 H16 H15)).
  generalize (Rplus_lt_compat_l 3 0 1 Rlt_0_1); rewrite Rplus_0_r.
  replace (3 + 1) with 4.
  intro; assumption.
  ring.
  symmetry  in |- *; rewrite <- Rmult_assoc; apply Rinv_r_simpl_m.
  discrR.
  ring.
  rewrite <- (Zplus_opp_l 2) in H13; generalize (Zplus_reg_l (-2) k0 2 H13);
    intro; assumption.
  split.
  assumption.
  apply Rle_lt_trans with (IZR (-2) + 3 * / 2).
  assumption.
  simpl in |- *; replace (-2 + 3 * / 2) with (- (1 * / 2)).
  apply Rlt_trans with 0.
  rewrite <- Ropp_0; apply Ropp_lt_gt_contravar.
  apply Rmult_lt_0_compat;
    [ apply Rlt_0_1 | apply Rinv_0_lt_compat; prove_sup0 ].
  apply Rlt_0_1.
  rewrite Rmult_1_l; apply Rmult_eq_reg_l with 2.
  rewrite Ropp_mult_distr_r_reverse; rewrite <- Rinv_r_sym.
  rewrite Rmult_plus_distr_l; rewrite <- Rmult_assoc; rewrite Rinv_r_simpl_m.
  ring.
  discrR.
  discrR.
  discrR.
  simpl in |- *; ring.
  simpl in |- *; ring.
  apply PI_neq0.
  unfold Rdiv in |- *; pattern 3 at 1 in |- *; rewrite (Rmult_comm 3);
    repeat rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; apply Rmult_comm.
  apply PI_neq0.
  symmetry  in |- *; rewrite (Rmult_comm (/ PI)); rewrite Rmult_assoc;
    rewrite <- Rinv_r_sym.
  apply Rmult_1_r.
  apply PI_neq0.
  rewrite double; pattern PI at 3 4 in |- *; rewrite double_var; ring.
  ring.
  pattern PI at 1 in |- *; rewrite double_var; ring.
Qed.

Lemma cos_eq_0_2PI_1 :
  forall x:R,
    0 <= x -> x <= 2 * PI -> x = PI / 2 \/ x = 3 * (PI / 2) -> cos x = 0.
Proof.
  intros x H1 H2 H3; elim H3; intro H4;
    [ rewrite H4; rewrite cos_PI2; reflexivity
      | rewrite H4; rewrite cos_3PI2; reflexivity ].
Qed.
