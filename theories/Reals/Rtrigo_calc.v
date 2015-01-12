(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo1.
Require Import R_sqrt.
Local Open Scope R_scope.

Lemma tan_PI : tan PI = 0.
Proof.
  unfold tan; rewrite sin_PI; rewrite cos_PI; unfold Rdiv;
    apply Rmult_0_l.
Qed.

Lemma sin_3PI2 : sin (3 * (PI / 2)) = -1.
Proof.
  replace (3 * (PI / 2)) with (PI + PI / 2).
  rewrite sin_plus; rewrite sin_PI; rewrite cos_PI; rewrite sin_PI2; ring.
  pattern PI at 1; rewrite (double_var PI); ring.
Qed.

Lemma tan_2PI : tan (2 * PI) = 0.
Proof.
  unfold tan; rewrite sin_2PI; unfold Rdiv; apply Rmult_0_l.
Qed.

Lemma sin_cos_PI4 : sin (PI / 4) = cos (PI / 4).
Proof with trivial.
  rewrite cos_sin...
  replace (PI / 2 + PI / 4) with (- (PI / 4) + PI)...
  rewrite neg_sin; rewrite sin_neg; ring...
  cut (PI = PI / 2 + PI / 2); [ intro | apply double_var ]...
  pattern PI at 2 3; rewrite H; pattern PI at 2 3; rewrite H...
  assert (H0 : 2 <> 0);
    [ discrR | unfold Rdiv; rewrite Rinv_mult_distr; try ring ]...
Qed.

Lemma sin_PI3_cos_PI6 : sin (PI / 3) = cos (PI / 6).
Proof with trivial.
  replace (PI / 6) with (PI / 2 - PI / 3)...
  rewrite cos_shift...
  assert (H0 : 6 <> 0); [ discrR | idtac ]...
  assert (H1 : 3 <> 0); [ discrR | idtac ]...
  assert (H2 : 2 <> 0); [ discrR | idtac ]...
  apply Rmult_eq_reg_l with 6...
  rewrite Rmult_minus_distr_l; repeat rewrite (Rmult_comm 6)...
  unfold Rdiv; repeat rewrite Rmult_assoc...
  rewrite <- Rinv_l_sym...
  rewrite (Rmult_comm (/ 3)); repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym...
  rewrite (Rmult_comm PI); repeat rewrite Rmult_1_r;
    repeat rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym...
  ring...
Qed.

Lemma sin_PI6_cos_PI3 : cos (PI / 3) = sin (PI / 6).
Proof with trivial.
  replace (PI / 6) with (PI / 2 - PI / 3)...
  rewrite sin_shift...
  assert (H0 : 6 <> 0); [ discrR | idtac ]...
  assert (H1 : 3 <> 0); [ discrR | idtac ]...
  assert (H2 : 2 <> 0); [ discrR | idtac ]...
  apply Rmult_eq_reg_l with 6...
  rewrite Rmult_minus_distr_l; repeat rewrite (Rmult_comm 6)...
  unfold Rdiv; repeat rewrite Rmult_assoc...
  rewrite <- Rinv_l_sym...
  rewrite (Rmult_comm (/ 3)); repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym...
  rewrite (Rmult_comm PI); repeat rewrite Rmult_1_r;
    repeat rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym...
  ring...
Qed.

Lemma PI6_RGT_0 : 0 < PI / 6.
Proof.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply PI_RGT_0 | apply Rinv_0_lt_compat; prove_sup0 ].
Qed.

Lemma PI6_RLT_PI2 : PI / 6 < PI / 2.
Proof.
  unfold Rdiv; apply Rmult_lt_compat_l.
  apply PI_RGT_0.
  apply Rinv_lt_contravar; prove_sup.
Qed.

Lemma sin_PI6 : sin (PI / 6) = 1 / 2.
Proof with trivial.
  assert (H : 2 <> 0); [ discrR | idtac ]...
  apply Rmult_eq_reg_l with (2 * cos (PI / 6))...
  replace (2 * cos (PI / 6) * sin (PI / 6)) with
  (2 * sin (PI / 6) * cos (PI / 6))...
  rewrite <- sin_2a; replace (2 * (PI / 6)) with (PI / 3)...
  rewrite sin_PI3_cos_PI6...
  unfold Rdiv; rewrite Rmult_1_l; rewrite Rmult_assoc;
    pattern 2 at 2; rewrite (Rmult_comm 2); rewrite Rmult_assoc;
      rewrite <- Rinv_l_sym...
  rewrite Rmult_1_r...
  unfold Rdiv; rewrite Rinv_mult_distr...
  rewrite (Rmult_comm (/ 2)); rewrite (Rmult_comm 2);
    repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym...
  rewrite Rmult_1_r...
  discrR...
  ring...
  apply prod_neq_R0...
  cut (0 < cos (PI / 6));
    [ intro H1; auto with real
      | apply cos_gt_0;
        [ apply (Rlt_trans (- (PI / 2)) 0 (PI / 6) _PI2_RLT_0 PI6_RGT_0)
          | apply PI6_RLT_PI2 ] ]...
Qed.

Lemma sqrt2_neq_0 : sqrt 2 <> 0.
Proof.
  assert (Hyp : 0 < 2);
    [ prove_sup0
      | generalize (Rlt_le 0 2 Hyp); intro H1; red; intro H2;
        generalize (sqrt_eq_0 2 H1 H2); intro H; absurd (2 = 0);
          [ discrR | assumption ] ].
Qed.

Lemma R1_sqrt2_neq_0 : 1 / sqrt 2 <> 0.
Proof.
  generalize (Rinv_neq_0_compat (sqrt 2) sqrt2_neq_0); intro H;
    generalize (prod_neq_R0 1 (/ sqrt 2) R1_neq_R0 H);
      intro H0; assumption.
Qed.

Lemma sqrt3_2_neq_0 : 2 * sqrt 3 <> 0.
Proof.
  apply prod_neq_R0;
    [ discrR
      | assert (Hyp : 0 < 3);
        [ prove_sup0
          | generalize (Rlt_le 0 3 Hyp); intro H1; red; intro H2;
            generalize (sqrt_eq_0 3 H1 H2); intro H; absurd (3 = 0);
              [ discrR | assumption ] ] ].
Qed.

Lemma Rlt_sqrt2_0 : 0 < sqrt 2.
Proof.
  assert (Hyp : 0 < 2);
    [ prove_sup0
      | generalize (sqrt_positivity 2 (Rlt_le 0 2 Hyp)); intro H1; elim H1;
        intro H2;
          [ assumption
            | absurd (0 = sqrt 2);
              [ apply (not_eq_sym (A:=R)); apply sqrt2_neq_0 | assumption ] ] ].
Qed.

Lemma Rlt_sqrt3_0 : 0 < sqrt 3.
Proof.
  cut (0%nat <> 1%nat);
    [ intro H0; assert (Hyp : 0 < 2);
      [ prove_sup0
        | generalize (Rlt_le 0 2 Hyp); intro H1; assert (Hyp2 : 0 < 3);
          [ prove_sup0
            | generalize (Rlt_le 0 3 Hyp2); intro H2;
              generalize (lt_INR_0 1 (neq_O_lt 1 H0));
                unfold INR; intro H3;
                  generalize (Rplus_lt_compat_l 2 0 1 H3);
                    rewrite Rplus_comm; rewrite Rplus_0_l; replace (2 + 1) with 3;
                      [ intro H4; generalize (sqrt_lt_1 2 3 H1 H2 H4); clear H3; intro H3;
                        apply (Rlt_trans 0 (sqrt 2) (sqrt 3) Rlt_sqrt2_0 H3)
                        | ring ] ] ]
      | discriminate ].
Qed.

Lemma PI4_RGT_0 : 0 < PI / 4.
Proof.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply PI_RGT_0 | apply Rinv_0_lt_compat; prove_sup0 ].
Qed.

Lemma cos_PI4 : cos (PI / 4) = 1 / sqrt 2.
Proof with trivial.
  apply Rsqr_inj...
  apply cos_ge_0...
  left; apply (Rlt_trans (- (PI / 2)) 0 (PI / 4) _PI2_RLT_0 PI4_RGT_0)...
  left; apply PI4_RLT_PI2...
  left; apply (Rmult_lt_0_compat 1 (/ sqrt 2))...
  prove_sup...
  apply Rinv_0_lt_compat; apply Rlt_sqrt2_0...
  rewrite Rsqr_div...
  rewrite Rsqr_1; rewrite Rsqr_sqrt...
  assert (H : 2 <> 0); [ discrR | idtac ]...
  unfold Rsqr; pattern (cos (PI / 4)) at 1;
    rewrite <- sin_cos_PI4;
      replace (sin (PI / 4) * cos (PI / 4)) with
      (1 / 2 * (2 * sin (PI / 4) * cos (PI / 4)))...
  rewrite <- sin_2a; replace (2 * (PI / 4)) with (PI / 2)...
  rewrite sin_PI2...
  apply Rmult_1_r...
  unfold Rdiv; rewrite (Rmult_comm 2); rewrite Rinv_mult_distr...
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym...
  rewrite Rmult_1_r...
  unfold Rdiv; rewrite Rmult_1_l; repeat rewrite <- Rmult_assoc...
  rewrite <- Rinv_l_sym...
  rewrite Rmult_1_l...
  left; prove_sup...
  apply sqrt2_neq_0...
Qed.

Lemma sin_PI4 : sin (PI / 4) = 1 / sqrt 2.
Proof.
  rewrite sin_cos_PI4; apply cos_PI4.
Qed.

Lemma tan_PI4 : tan (PI / 4) = 1.
Proof.
  unfold tan; rewrite sin_cos_PI4.
  unfold Rdiv; apply Rinv_r.
  change (cos (PI / 4) <> 0); rewrite cos_PI4; apply R1_sqrt2_neq_0.
Qed.

Lemma cos3PI4 : cos (3 * (PI / 4)) = -1 / sqrt 2.
Proof with trivial.
  replace (3 * (PI / 4)) with (PI / 2 - - (PI / 4))...
  rewrite cos_shift; rewrite sin_neg; rewrite sin_PI4...
  unfold Rdiv; rewrite Ropp_mult_distr_l_reverse...
  unfold Rminus; rewrite Ropp_involutive; pattern PI at 1;
    rewrite double_var; unfold Rdiv; rewrite Rmult_plus_distr_r;
      repeat rewrite Rmult_assoc; rewrite <- Rinv_mult_distr;
        [ ring | discrR | discrR ]...
Qed.

Lemma sin3PI4 : sin (3 * (PI / 4)) = 1 / sqrt 2.
Proof with trivial.
  replace (3 * (PI / 4)) with (PI / 2 - - (PI / 4))...
  rewrite sin_shift; rewrite cos_neg; rewrite cos_PI4...
  unfold Rminus; rewrite Ropp_involutive; pattern PI at 1;
    rewrite double_var; unfold Rdiv; rewrite Rmult_plus_distr_r;
      repeat rewrite Rmult_assoc; rewrite <- Rinv_mult_distr;
        [ ring | discrR | discrR ]...
Qed.

Lemma cos_PI6 : cos (PI / 6) = sqrt 3 / 2.
Proof with trivial.
  apply Rsqr_inj...
  apply cos_ge_0...
  left; apply (Rlt_trans (- (PI / 2)) 0 (PI / 6) _PI2_RLT_0 PI6_RGT_0)...
  left; apply PI6_RLT_PI2...
  left; apply (Rmult_lt_0_compat (sqrt 3) (/ 2))...
  apply Rlt_sqrt3_0...
  apply Rinv_0_lt_compat; prove_sup0...
  assert (H : 2 <> 0); [ discrR | idtac ]...
  assert (H1 : 4 <> 0); [ apply prod_neq_R0 | idtac ]...
  rewrite Rsqr_div...
  rewrite cos2; unfold Rsqr; rewrite sin_PI6; rewrite sqrt_def...
  unfold Rdiv; rewrite Rmult_1_l; apply Rmult_eq_reg_l with 4...
  rewrite Rmult_minus_distr_l; rewrite (Rmult_comm 3);
    repeat rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym...
  rewrite Rmult_1_l; rewrite Rmult_1_r...
  rewrite <- (Rmult_comm (/ 2)); repeat rewrite <- Rmult_assoc...
  rewrite <- Rinv_l_sym...
  rewrite Rmult_1_l; rewrite <- Rinv_r_sym...
  ring...
  left; prove_sup0...
Qed.

Lemma tan_PI6 : tan (PI / 6) = 1 / sqrt 3.
Proof.
  unfold tan; rewrite sin_PI6; rewrite cos_PI6; unfold Rdiv;
    repeat rewrite Rmult_1_l; rewrite Rinv_mult_distr.
  rewrite Rinv_involutive.
  rewrite (Rmult_comm (/ 2)); rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  apply Rmult_1_r.
  discrR.
  discrR.
  red; intro; assert (H1 := Rlt_sqrt3_0); rewrite H in H1;
    elim (Rlt_irrefl 0 H1).
  apply Rinv_neq_0_compat; discrR.
Qed.

Lemma sin_PI3 : sin (PI / 3) = sqrt 3 / 2.
Proof.
  rewrite sin_PI3_cos_PI6; apply cos_PI6.
Qed.

Lemma cos_PI3 : cos (PI / 3) = 1 / 2.
Proof.
  rewrite sin_PI6_cos_PI3; apply sin_PI6.
Qed.

Lemma tan_PI3 : tan (PI / 3) = sqrt 3.
Proof.
  unfold tan; rewrite sin_PI3; rewrite cos_PI3; unfold Rdiv;
    rewrite Rmult_1_l; rewrite Rinv_involutive.
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  apply Rmult_1_r.
  discrR.
  discrR.
Qed.

Lemma sin_2PI3 : sin (2 * (PI / 3)) = sqrt 3 / 2.
Proof.
  rewrite double; rewrite sin_plus; rewrite sin_PI3; rewrite cos_PI3;
    unfold Rdiv; repeat rewrite Rmult_1_l; rewrite (Rmult_comm (/ 2));
      repeat rewrite <- Rmult_assoc; rewrite double_var;
        reflexivity.
Qed.

Lemma cos_2PI3 : cos (2 * (PI / 3)) = -1 / 2.
Proof with trivial.
  assert (H : 2 <> 0); [ discrR | idtac ]...
  assert (H0 : 4 <> 0); [ apply prod_neq_R0 | idtac ]...
  rewrite double; rewrite cos_plus; rewrite sin_PI3; rewrite cos_PI3;
    unfold Rdiv; rewrite Rmult_1_l; apply Rmult_eq_reg_l with 4...
  rewrite Rmult_minus_distr_l; repeat rewrite Rmult_assoc;
    rewrite (Rmult_comm 2)...
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym...
  rewrite Rmult_1_r; rewrite <- Rinv_r_sym...
  pattern 2 at 4; rewrite (Rmult_comm 2); repeat rewrite Rmult_assoc;
    rewrite <- Rinv_l_sym...
  rewrite Rmult_1_r; rewrite Ropp_mult_distr_r_reverse; rewrite Rmult_1_r...
  rewrite (Rmult_comm 2); repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym...
  rewrite Rmult_1_r; rewrite (Rmult_comm 2); rewrite (Rmult_comm (/ 2))...
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym...
  rewrite Rmult_1_r; rewrite sqrt_def...
  ring...
  left; prove_sup...
Qed.

Lemma tan_2PI3 : tan (2 * (PI / 3)) = - sqrt 3.
Proof with trivial.
  assert (H : 2 <> 0); [ discrR | idtac ]...
  unfold tan; rewrite sin_2PI3; rewrite cos_2PI3; unfold Rdiv;
    rewrite Ropp_mult_distr_l_reverse; rewrite Rmult_1_l;
      rewrite <- Ropp_inv_permute...
  rewrite Rinv_involutive...
  rewrite Rmult_assoc; rewrite Ropp_mult_distr_r_reverse; rewrite <- Rinv_l_sym...
  ring...
  apply Rinv_neq_0_compat...
Qed.

Lemma cos_5PI4 : cos (5 * (PI / 4)) = -1 / sqrt 2.
Proof with trivial.
  replace (5 * (PI / 4)) with (PI / 4 + PI)...
  rewrite neg_cos; rewrite cos_PI4; unfold Rdiv;
    rewrite Ropp_mult_distr_l_reverse...
  pattern PI at 2; rewrite double_var; pattern PI at 2 3;
    rewrite double_var; assert (H : 2 <> 0);
      [ discrR | unfold Rdiv; repeat rewrite Rinv_mult_distr; try ring ]...
Qed.

Lemma sin_5PI4 : sin (5 * (PI / 4)) = -1 / sqrt 2.
Proof with trivial.
  replace (5 * (PI / 4)) with (PI / 4 + PI)...
  rewrite neg_sin; rewrite sin_PI4; unfold Rdiv;
    rewrite Ropp_mult_distr_l_reverse...
  pattern PI at 2; rewrite double_var; pattern PI at 2 3;
    rewrite double_var; assert (H : 2 <> 0);
      [ discrR | unfold Rdiv; repeat rewrite Rinv_mult_distr; try ring ]...
Qed.

Lemma sin_cos5PI4 : cos (5 * (PI / 4)) = sin (5 * (PI / 4)).
Proof.
  rewrite cos_5PI4; rewrite sin_5PI4; reflexivity.
Qed.

Lemma Rgt_3PI2_0 : 0 < 3 * (PI / 2).
Proof.
  apply Rmult_lt_0_compat;
    [ prove_sup0
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ apply PI_RGT_0 | apply Rinv_0_lt_compat; prove_sup0 ] ].
Qed.

Lemma Rgt_2PI_0 : 0 < 2 * PI.
Proof.
  apply Rmult_lt_0_compat; [ prove_sup0 | apply PI_RGT_0 ].
Qed.

Lemma Rlt_PI_3PI2 : PI < 3 * (PI / 2).
Proof.
  generalize PI2_RGT_0; intro H1;
    generalize (Rplus_lt_compat_l PI 0 (PI / 2) H1);
      replace (PI + PI / 2) with (3 * (PI / 2)).
  rewrite Rplus_0_r; intro H2; assumption.
  pattern PI at 2; rewrite double_var; ring.
Qed.

Lemma Rlt_3PI2_2PI : 3 * (PI / 2) < 2 * PI.
Proof.
  generalize PI2_RGT_0; intro H1;
    generalize (Rplus_lt_compat_l (3 * (PI / 2)) 0 (PI / 2) H1);
      replace (3 * (PI / 2) + PI / 2) with (2 * PI).
  rewrite Rplus_0_r; intro H2; assumption.
  rewrite double; pattern PI at 1 2; rewrite double_var; ring.
Qed.

(***************************************************************)
(** Radian -> Degree | Degree -> Radian                        *)
(***************************************************************)

Definition plat : R := 180.
Definition toRad (x:R) : R := x * PI * / plat.
Definition toDeg (x:R) : R := x * plat * / PI.

Lemma rad_deg : forall x:R, toRad (toDeg x) = x.
Proof.
  intro; unfold toRad, toDeg;
    replace (x * plat * / PI * PI * / plat) with
    (x * (plat * / plat) * (PI * / PI)); [ idtac | ring ].
  repeat rewrite <- Rinv_r_sym.
  ring.
  apply PI_neq0.
  unfold plat; discrR.
Qed.

Lemma toRad_inj : forall x y:R, toRad x = toRad y -> x = y.
Proof.
  intros; unfold toRad in H; apply Rmult_eq_reg_l with PI.
  rewrite <- (Rmult_comm x); rewrite <- (Rmult_comm y).
  apply Rmult_eq_reg_l with (/ plat).
  rewrite <- (Rmult_comm (x * PI)); rewrite <- (Rmult_comm (y * PI));
    assumption.
  apply Rinv_neq_0_compat; unfold plat; discrR.
  apply PI_neq0.
Qed.

Lemma deg_rad : forall x:R, toDeg (toRad x) = x.
Proof.
  intro x; apply toRad_inj; rewrite (rad_deg (toRad x)); reflexivity.
Qed.

Definition sind (x:R) : R := sin (toRad x).
Definition cosd (x:R) : R := cos (toRad x).
Definition tand (x:R) : R := tan (toRad x).

Lemma Rsqr_sin_cos_d_one : forall x:R, Rsqr (sind x) + Rsqr (cosd x) = 1.
Proof.
  intro x; unfold sind; unfold cosd; apply sin2_cos2.
Qed.

(***************************************************)
(**               Other properties                 *)
(***************************************************)

Lemma sin_lb_ge_0 : forall a:R, 0 <= a -> a <= PI / 2 -> 0 <= sin_lb a.
Proof.
  intros; case (Rtotal_order 0 a); intro.
  left; apply sin_lb_gt_0; assumption.
  elim H1; intro.
  rewrite <- H2; unfold sin_lb; unfold sin_approx;
    unfold sum_f_R0; unfold sin_term;
      repeat rewrite pow_ne_zero.
  unfold Rdiv; repeat rewrite Rmult_0_l; repeat rewrite Rmult_0_r;
    repeat rewrite Rplus_0_r; right; reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  elim (Rlt_irrefl 0 (Rle_lt_trans 0 a 0 H H2)).
Qed.
