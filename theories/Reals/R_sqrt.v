(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import Rsqrt_def.
Open Local Scope R_scope.

(** * Continuous extension of Rsqrt on R *)
Definition sqrt (x:R) : R :=
  match Rcase_abs x with
    | left _ => 0
    | right a => Rsqrt (mknonnegreal x (Rge_le _ _ a))
  end.

Lemma sqrt_pos : forall x : R, 0 <= sqrt x.
Proof.
  intros x.
  unfold sqrt.
  destruct (Rcase_abs x) as [H|H].
  apply Rle_refl.
  apply Rsqrt_positivity.
Qed.

Lemma sqrt_positivity : forall x:R, 0 <= x -> 0 <= sqrt x.
Proof.
  intros x _.
  apply sqrt_pos.
Qed.

Lemma sqrt_sqrt : forall x:R, 0 <= x -> sqrt x * sqrt x = x.
Proof.
  intros.
  unfold sqrt in |- *.
  case (Rcase_abs x); intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ r H)).
  rewrite Rsqrt_Rsqrt; reflexivity.
Qed.

Lemma sqrt_0 : sqrt 0 = 0.
Proof.
  apply Rsqr_eq_0; unfold Rsqr in |- *; apply sqrt_sqrt; right; reflexivity.
Qed.

Lemma sqrt_1 : sqrt 1 = 1.
Proof.
  apply (Rsqr_inj (sqrt 1) 1);
    [ apply sqrt_positivity; left
      | left
      | unfold Rsqr in |- *; rewrite sqrt_sqrt; [ ring | left ] ];
    apply Rlt_0_1.
Qed.

Lemma sqrt_eq_0 : forall x:R, 0 <= x -> sqrt x = 0 -> x = 0.
Proof.
  intros; cut (Rsqr (sqrt x) = 0).
  intro; unfold Rsqr in H1; rewrite sqrt_sqrt in H1; assumption.
  rewrite H0; apply Rsqr_0.
Qed.

Lemma sqrt_lem_0 : forall x y:R, 0 <= x -> 0 <= y -> sqrt x = y -> y * y = x.
Proof.
  intros; rewrite <- H1; apply (sqrt_sqrt x H).
Qed.

Lemma sqrt_lem_1 : forall x y:R, 0 <= x -> 0 <= y -> y * y = x -> sqrt x = y.
Proof.
  intros; apply Rsqr_inj;
    [ apply (sqrt_positivity x H)
      | assumption
      | unfold Rsqr in |- *; rewrite H1; apply (sqrt_sqrt x H) ].
Qed.

Lemma sqrt_def : forall x:R, 0 <= x -> sqrt x * sqrt x = x.
Proof.
  intros; apply (sqrt_sqrt x H).
Qed.

Lemma sqrt_square : forall x:R, 0 <= x -> sqrt (x * x) = x.
Proof.
  intros;
    apply
      (Rsqr_inj (sqrt (Rsqr x)) x (sqrt_positivity (Rsqr x) (Rle_0_sqr x)) H);
      unfold Rsqr in |- *; apply (sqrt_sqrt (Rsqr x) (Rle_0_sqr x)).
Qed.

Lemma sqrt_Rsqr : forall x:R, 0 <= x -> sqrt (Rsqr x) = x.
Proof.
  intros; unfold Rsqr in |- *; apply sqrt_square; assumption.
Qed.

Lemma sqrt_Rsqr_abs : forall x:R, sqrt (Rsqr x) = Rabs x.
Proof.
  intro x; rewrite Rsqr_abs; apply sqrt_Rsqr; apply Rabs_pos.
Qed.

Lemma Rsqr_sqrt : forall x:R, 0 <= x -> Rsqr (sqrt x) = x.
Proof.
  intros x H1; unfold Rsqr in |- *; apply (sqrt_sqrt x H1).
Qed.

Lemma sqrt_mult_alt :
  forall x y : R, 0 <= x -> sqrt (x * y) = sqrt x * sqrt y.
Proof.
  intros x y Hx.
  unfold sqrt at 3.
  destruct (Rcase_abs y) as [Hy|Hy].
  rewrite Rmult_0_r.
  destruct Hx as [Hx'|Hx'].
  unfold sqrt.
  destruct (Rcase_abs (x * y)) as [Hxy|Hxy].
  apply eq_refl.
  elim Rge_not_lt with (1 := Hxy).
  rewrite <- (Rmult_0_r x).
  now apply Rmult_lt_compat_l.
  rewrite <- Hx', Rmult_0_l.
  exact sqrt_0.
  apply Rsqr_inj.
  apply sqrt_pos.
  apply Rmult_le_pos.
  apply sqrt_pos.
  apply Rsqrt_positivity.
  rewrite Rsqr_mult, 2!Rsqr_sqrt.
  unfold Rsqr.
  now rewrite Rsqrt_Rsqrt.
  exact Hx.
  apply Rmult_le_pos.
  exact Hx.
  now apply Rge_le.
Qed.

Lemma sqrt_mult :
  forall x y:R, 0 <= x -> 0 <= y -> sqrt (x * y) = sqrt x * sqrt y.
Proof.
  intros x y Hx _.
  now apply sqrt_mult_alt.
Qed.

Lemma sqrt_lt_R0 : forall x:R, 0 < x -> 0 < sqrt x.
Proof.
  intros x H1; apply Rsqr_incrst_0;
    [ rewrite Rsqr_0; rewrite Rsqr_sqrt; [ assumption | left; assumption ]
      | right; reflexivity
      | apply (sqrt_positivity x (Rlt_le 0 x H1)) ].
Qed.

Lemma sqrt_div_alt :
  forall x y : R, 0 < y -> sqrt (x / y) = sqrt x / sqrt y.
Proof.
  intros x y Hy.
  unfold sqrt at 2.
  destruct (Rcase_abs x) as [Hx|Hx].
  unfold Rdiv.
  rewrite Rmult_0_l.
  unfold sqrt.
  destruct (Rcase_abs (x * / y)) as [Hxy|Hxy].
  apply eq_refl.
  elim Rge_not_lt with (1 := Hxy).
  apply Rmult_lt_reg_r with y.
  exact Hy.
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_0_l.
  exact Hx.
  now apply Rgt_not_eq.
  set (Hx' := Rge_le x 0 Hx).
  clearbody Hx'. clear Hx.
  apply Rsqr_inj.
  apply sqrt_pos.
  apply Fourier_util.Rle_mult_inv_pos.
  apply Rsqrt_positivity.
  now apply sqrt_lt_R0.
  rewrite Rsqr_div, 2!Rsqr_sqrt.
  unfold Rsqr.
  now rewrite Rsqrt_Rsqrt.
  now apply Rlt_le.
  now apply Fourier_util.Rle_mult_inv_pos.
  apply Rgt_not_eq.
  now apply sqrt_lt_R0.
Qed.

Lemma sqrt_div :
  forall x y:R, 0 <= x -> 0 < y -> sqrt (x / y) = sqrt x / sqrt y.
Proof.
  intros x y _ H.
  now apply sqrt_div_alt.
Qed.

Lemma sqrt_lt_0_alt :
  forall x y : R, sqrt x < sqrt y -> x < y.
Proof.
  intros x y.
  unfold sqrt at 2.
  destruct (Rcase_abs y) as [Hy|Hy].
  intros Hx.
  elim Rlt_not_le with (1 := Hx).
  apply sqrt_pos.
  set (Hy' := Rge_le y 0 Hy).
  clearbody Hy'. clear Hy.
  unfold sqrt.
  destruct (Rcase_abs x) as [Hx|Hx].
  intros _.
  now apply Rlt_le_trans with R0.
  intros Hxy.
  apply Rsqr_incrst_1 in Hxy ; try apply Rsqrt_positivity.
  unfold Rsqr in Hxy.
  now rewrite 2!Rsqrt_Rsqrt in Hxy.
Qed.

Lemma sqrt_lt_0 : forall x y:R, 0 <= x -> 0 <= y -> sqrt x < sqrt y -> x < y.
Proof.
  intros x y _ _.
  apply sqrt_lt_0_alt.
Qed.

Lemma sqrt_lt_1_alt :
  forall x y : R, 0 <= x < y -> sqrt x < sqrt y.
Proof.
  intros x y (Hx, Hxy).
  apply Rsqr_incrst_0 ; try apply sqrt_pos.
  rewrite 2!Rsqr_sqrt.
  exact Hxy.
  apply Rlt_le.
  now apply Rle_lt_trans with x.
  exact Hx.
Qed.

Lemma sqrt_lt_1 : forall x y:R, 0 <= x -> 0 <= y -> x < y -> sqrt x < sqrt y.
Proof.
  intros x y Hx _ Hxy.
  apply sqrt_lt_1_alt.
  now split.
Qed.

Lemma sqrt_le_0 :
  forall x y:R, 0 <= x -> 0 <= y -> sqrt x <= sqrt y -> x <= y.
Proof.
  intros x y H1 H2 H3;
    generalize
      (Rsqr_incr_1 (sqrt x) (sqrt y) H3 (sqrt_positivity x H1)
        (sqrt_positivity y H2)); intro H4; rewrite (Rsqr_sqrt x H1) in H4;
      rewrite (Rsqr_sqrt y H2) in H4; assumption.
Qed.

Lemma sqrt_le_1_alt :
  forall x y : R, x <= y -> sqrt x <= sqrt y.
Proof.
  intros x y [Hxy|Hxy].
  destruct (Rle_or_lt 0 x) as [Hx|Hx].
  apply Rlt_le.
  apply sqrt_lt_1_alt.
  now split.
  unfold sqrt at 1.
  destruct (Rcase_abs x) as [Hx'|Hx'].
  apply sqrt_pos.
  now elim Rge_not_lt with (1 := Hx').
  rewrite Hxy.
  apply Rle_refl.
Qed.

Lemma sqrt_le_1 :
  forall x y:R, 0 <= x -> 0 <= y -> x <= y -> sqrt x <= sqrt y.
Proof.
  intros x y _ _ Hxy.
  now apply sqrt_le_1_alt.
Qed.

Lemma sqrt_inj : forall x y:R, 0 <= x -> 0 <= y -> sqrt x = sqrt y -> x = y.
Proof.
  intros; cut (Rsqr (sqrt x) = Rsqr (sqrt y)).
  intro; rewrite (Rsqr_sqrt x H) in H2; rewrite (Rsqr_sqrt y H0) in H2;
    assumption.
  rewrite H1; reflexivity.
Qed.

Lemma sqrt_less_alt :
  forall x : R, 1 < x -> sqrt x < x.
Proof.
  intros x Hx.
  assert (Hx1 := Rle_lt_trans _ _ _ Rle_0_1 Hx).
  assert (Hx2 := Rlt_le _ _ Hx1).
  apply Rsqr_incrst_0 ; trivial.
  rewrite Rsqr_sqrt ; trivial.
  rewrite <- (Rmult_1_l x) at 1.
  now apply Rmult_lt_compat_r.
  apply sqrt_pos.
Qed.

Lemma sqrt_less : forall x:R, 0 <= x -> 1 < x -> sqrt x < x.
Proof.
  intros x _.
  apply sqrt_less_alt.
Qed.

Lemma sqrt_more : forall x:R, 0 < x -> x < 1 -> x < sqrt x.
Proof.
  intros x H1 H2;
    generalize (sqrt_lt_1 x 1 (Rlt_le 0 x H1) (Rlt_le 0 1 Rlt_0_1) H2);
      intro H3; rewrite sqrt_1 in H3; generalize (Rmult_ne (sqrt x));
        intro H4; elim H4; intros H5 H6; rewrite <- H5; pattern x at 1 in |- *;
          rewrite <- (sqrt_def x (Rlt_le 0 x H1));
            apply (Rmult_lt_compat_l (sqrt x) (sqrt x) 1 (sqrt_lt_R0 x H1) H3).
Qed.

Lemma sqrt_cauchy :
  forall a b c d:R,
    a * c + b * d <= sqrt (Rsqr a + Rsqr b) * sqrt (Rsqr c + Rsqr d).
Proof.
  intros a b c d; apply Rsqr_incr_0_var;
    [ rewrite Rsqr_mult; repeat rewrite Rsqr_sqrt; unfold Rsqr in |- *;
      [ replace ((a * c + b * d) * (a * c + b * d)) with
        (a * a * c * c + b * b * d * d + 2 * a * b * c * d);
        [ replace ((a * a + b * b) * (c * c + d * d)) with
          (a * a * c * c + b * b * d * d + (a * a * d * d + b * b * c * c));
          [ apply Rplus_le_compat_l;
            replace (a * a * d * d + b * b * c * c) with
            (2 * a * b * c * d +
              (a * a * d * d + b * b * c * c - 2 * a * b * c * d));
            [ pattern (2 * a * b * c * d) at 1 in |- *; rewrite <- Rplus_0_r;
              apply Rplus_le_compat_l;
                replace (a * a * d * d + b * b * c * c - 2 * a * b * c * d)
              with (Rsqr (a * d - b * c));
                [ apply Rle_0_sqr | unfold Rsqr in |- *; ring ]
              | ring ]
            | ring ]
          | ring ]
        | apply
          (Rplus_le_le_0_compat (Rsqr c) (Rsqr d) (Rle_0_sqr c) (Rle_0_sqr d))
        | apply
          (Rplus_le_le_0_compat (Rsqr a) (Rsqr b) (Rle_0_sqr a) (Rle_0_sqr b)) ]
      | apply Rmult_le_pos; apply sqrt_positivity; apply Rplus_le_le_0_compat;
        apply Rle_0_sqr ].
Qed.

(************************************************************)
(** * Resolution of [a*X^2+b*X+c=0]                         *)
(************************************************************)

Definition Delta (a:nonzeroreal) (b c:R) : R := Rsqr b - 4 * a * c.

Definition Delta_is_pos (a:nonzeroreal) (b c:R) : Prop := 0 <= Delta a b c.

Definition sol_x1 (a:nonzeroreal) (b c:R) : R :=
  (- b + sqrt (Delta a b c)) / (2 * a).

Definition sol_x2 (a:nonzeroreal) (b c:R) : R :=
  (- b - sqrt (Delta a b c)) / (2 * a).

Lemma Rsqr_sol_eq_0_1 :
  forall (a:nonzeroreal) (b c x:R),
    Delta_is_pos a b c ->
    x = sol_x1 a b c \/ x = sol_x2 a b c -> a * Rsqr x + b * x + c = 0.
Proof.
  intros; elim H0; intro.
  unfold sol_x1 in H1; unfold Delta in H1; rewrite H1; unfold Rdiv in |- *;
    repeat rewrite Rsqr_mult; rewrite Rsqr_plus; rewrite <- Rsqr_neg;
      rewrite Rsqr_sqrt.
  rewrite Rsqr_inv.
  unfold Rsqr in |- *; repeat rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc; rewrite (Rmult_comm a).
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  pattern 2 at 2 in |- *; rewrite (Rmult_comm 2).
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite
    (Rmult_plus_distr_r (- b) (sqrt (b * b - 2 * (2 * (a * c)))) (/ 2 * / a))
    .
  rewrite Rmult_plus_distr_l; repeat rewrite Rplus_assoc.
  replace
  (- b * (sqrt (b * b - 2 * (2 * (a * c))) * (/ 2 * / a)) +
    (b * (- b * (/ 2 * / a)) +
      (b * (sqrt (b * b - 2 * (2 * (a * c))) * (/ 2 * / a)) + c))) with
  (b * (- b * (/ 2 * / a)) + c).
  unfold Rminus in |- *; repeat rewrite <- Rplus_assoc.
  replace (b * b + b * b) with (2 * (b * b)).
  rewrite Rmult_plus_distr_r; repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm 2); repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite Ropp_mult_distr_l_reverse; repeat rewrite Rmult_assoc;
    rewrite (Rmult_comm 2).
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite (Rmult_comm (/ 2)); repeat rewrite Rmult_assoc;
    rewrite (Rmult_comm 2).
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm a); rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite <- Rmult_opp_opp.
  ring.
  apply (cond_nonzero a).
  discrR.
  discrR.
  discrR.
  ring.
  ring.
  discrR.
  apply (cond_nonzero a).
  discrR.
  apply (cond_nonzero a).
  apply prod_neq_R0; [ discrR | apply (cond_nonzero a) ].
  apply prod_neq_R0; [ discrR | apply (cond_nonzero a) ].
  apply prod_neq_R0; [ discrR | apply (cond_nonzero a) ].
  assumption.
  unfold sol_x2 in H1; unfold Delta in H1; rewrite H1; unfold Rdiv in |- *;
    repeat rewrite Rsqr_mult; rewrite Rsqr_minus; rewrite <- Rsqr_neg;
      rewrite Rsqr_sqrt.
  rewrite Rsqr_inv.
  unfold Rsqr in |- *; repeat rewrite Rinv_mult_distr;
    repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm a); repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; unfold Rminus in |- *; rewrite Rmult_plus_distr_r.
  rewrite Ropp_mult_distr_l_reverse; repeat rewrite Rmult_assoc;
    pattern 2 at 2 in |- *; rewrite (Rmult_comm 2).
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r;
    rewrite
      (Rmult_plus_distr_r (- b) (- sqrt (b * b + - (2 * (2 * (a * c)))))
        (/ 2 * / a)).
  rewrite Rmult_plus_distr_l; repeat rewrite Rplus_assoc.
  rewrite Ropp_mult_distr_l_reverse; rewrite Ropp_involutive.
  replace
  (b * (sqrt (b * b + - (2 * (2 * (a * c)))) * (/ 2 * / a)) +
    (b * (- b * (/ 2 * / a)) +
      (b * (- sqrt (b * b + - (2 * (2 * (a * c)))) * (/ 2 * / a)) + c))) with
  (b * (- b * (/ 2 * / a)) + c).
  repeat rewrite <- Rplus_assoc; replace (b * b + b * b) with (2 * (b * b)).
  rewrite Rmult_plus_distr_r; repeat rewrite Rmult_assoc;
    rewrite (Rmult_comm 2); repeat rewrite Rmult_assoc;
      rewrite <- Rinv_l_sym.
  rewrite Ropp_mult_distr_l_reverse; repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm 2); repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite (Rmult_comm (/ 2)); repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm 2); repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; repeat rewrite Rmult_assoc; rewrite (Rmult_comm a);
    rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite <- Rmult_opp_opp; ring.
  apply (cond_nonzero a).
  discrR.
  discrR.
  discrR.
  ring.
  ring.
  discrR.
  apply (cond_nonzero a).
  discrR.
  discrR.
  apply (cond_nonzero a).
  apply prod_neq_R0; discrR || apply (cond_nonzero a).
  apply prod_neq_R0; discrR || apply (cond_nonzero a).
  apply prod_neq_R0; discrR || apply (cond_nonzero a).
  assumption.
Qed.

Lemma Rsqr_sol_eq_0_0 :
  forall (a:nonzeroreal) (b c x:R),
    Delta_is_pos a b c ->
    a * Rsqr x + b * x + c = 0 -> x = sol_x1 a b c \/ x = sol_x2 a b c.
Proof.
  intros; rewrite (canonical_Rsqr a b c x) in H0; rewrite Rplus_comm in H0;
    generalize
      (Rplus_opp_r_uniq ((4 * a * c - Rsqr b) / (4 * a))
        (a * Rsqr (x + b / (2 * a))) H0); cut (Rsqr b - 4 * a * c = Delta a b c).
  intro;
    replace (- ((4 * a * c - Rsqr b) / (4 * a))) with
    ((Rsqr b - 4 * a * c) / (4 * a)).
  rewrite H1; intro;
    generalize
      (Rmult_eq_compat_l (/ a) (a * Rsqr (x + b / (2 * a)))
        (Delta a b c / (4 * a)) H2);
      replace (/ a * (a * Rsqr (x + b / (2 * a)))) with (Rsqr (x + b / (2 * a))).
  replace (/ a * (Delta a b c / (4 * a))) with
  (Rsqr (sqrt (Delta a b c) / (2 * a))).
  intro;
    generalize (Rsqr_eq (x + b / (2 * a)) (sqrt (Delta a b c) / (2 * a)) H3);
      intro; elim H4; intro.
  left; unfold sol_x1 in |- *;
    generalize
      (Rplus_eq_compat_l (- (b / (2 * a))) (x + b / (2 * a))
        (sqrt (Delta a b c) / (2 * a)) H5);
      replace (- (b / (2 * a)) + (x + b / (2 * a))) with x.
  intro; rewrite H6; unfold Rdiv in |- *; ring.
  ring.
  right; unfold sol_x2 in |- *;
    generalize
      (Rplus_eq_compat_l (- (b / (2 * a))) (x + b / (2 * a))
        (- (sqrt (Delta a b c) / (2 * a))) H5);
      replace (- (b / (2 * a)) + (x + b / (2 * a))) with x.
  intro; rewrite H6; unfold Rdiv in |- *; ring.
  ring.
  rewrite Rsqr_div.
  rewrite Rsqr_sqrt.
  unfold Rdiv in |- *.
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (/ a)).
  rewrite Rmult_assoc.
  rewrite <- Rinv_mult_distr.
  replace (2 * (2 * a) * a) with (Rsqr (2 * a)).
  reflexivity.
  ring_Rsqr.
  rewrite <- Rmult_assoc; apply prod_neq_R0;
    [ discrR | apply (cond_nonzero a) ].
  apply (cond_nonzero a).
  assumption.
  apply prod_neq_R0; [ discrR | apply (cond_nonzero a) ].
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  symmetry  in |- *; apply Rmult_1_l.
  apply (cond_nonzero a).
  unfold Rdiv in |- *; rewrite <- Ropp_mult_distr_l_reverse.
  rewrite Ropp_minus_distr.
  reflexivity.
  reflexivity.
Qed.
