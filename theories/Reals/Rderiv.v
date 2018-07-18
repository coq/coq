(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*********************************************************)
(**     Definition of the derivative,continuity          *)
(*                                                       *)
(*********************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import Rlimit.
Require Import Lra.
Require Import Omega.
Local Open Scope R_scope.

(*********)
Definition D_x (D:R -> Prop) (y x:R) : Prop := D x /\ y <> x.

(*********)
Definition continue_in (f:R -> R) (D:R -> Prop) (x0:R) : Prop :=
  limit1_in f (D_x D x0) (f x0) x0.

(*********)
Definition D_in (f d:R -> R) (D:R -> Prop) (x0:R) : Prop :=
  limit1_in (fun x:R => (f x - f x0) / (x - x0)) (D_x D x0) (d x0) x0.

(*********)
Lemma cont_deriv :
  forall (f d:R -> R) (D:R -> Prop) (x0:R),
    D_in f d D x0 -> continue_in f D x0.
Proof.
  unfold continue_in; unfold D_in; unfold limit1_in;
    unfold limit_in; unfold Rdiv; simpl;
      intros; elim (H eps H0); clear H; intros; elim H;
        clear H; intros; elim (Req_dec (d x0) 0); intro.
  split with (Rmin 1 x); split.
  elim (Rmin_Rgt 1 x 0); intros a b; apply (b (conj Rlt_0_1 H)).
  intros; elim H3; clear H3; intros;
    generalize (let (H1, H2) := Rmin_Rgt 1 x (R_dist x1 x0) in H1);
      unfold Rgt; intro; elim (H5 H4); clear H5;
        intros; generalize (H1 x1 (conj H3 H6)); clear H1;
          intro; unfold D_x in H3; elim H3; intros.
  rewrite H2 in H1; unfold R_dist; unfold R_dist in H1;
    cut (Rabs (f x1 - f x0) < eps * Rabs (x1 - x0)).
  intro; unfold R_dist in H5;
    generalize (Rmult_lt_compat_l eps (Rabs (x1 - x0)) 1 H0 H5);
      rewrite Rmult_1_r; intro; apply Rlt_trans with (r2 := eps * Rabs (x1 - x0));
        assumption.
  rewrite (Rminus_0_r ((f x1 - f x0) * / (x1 - x0))) in H1;
    rewrite Rabs_mult in H1; cut (x1 - x0 <> 0).
  intro; rewrite (Rabs_Rinv (x1 - x0) H9) in H1;
    generalize
      (Rmult_lt_compat_l (Rabs (x1 - x0)) (Rabs (f x1 - f x0) * / Rabs (x1 - x0))
        eps (Rabs_pos_lt (x1 - x0) H9) H1); intro; rewrite Rmult_comm in H10;
      rewrite Rmult_assoc in H10; rewrite Rinv_l in H10.
  rewrite Rmult_1_r in H10; rewrite Rmult_comm; assumption.
  apply Rabs_no_R0; auto.
  apply Rminus_eq_contra; auto.
(**)
  split with (Rmin (Rmin (/ 2) x) (eps * / Rabs (2 * d x0))); split.
  cut (Rmin (/ 2) x > 0).
  cut (eps * / Rabs (2 * d x0) > 0).
  intros; elim (Rmin_Rgt (Rmin (/ 2) x) (eps * / Rabs (2 * d x0)) 0);
    intros a b; apply (b (conj H4 H3)).
  apply Rmult_gt_0_compat; auto.
  unfold Rgt; apply Rinv_0_lt_compat; apply Rabs_pos_lt;
    apply Rmult_integral_contrapositive; split.
  discrR.
  assumption.
  elim (Rmin_Rgt (/ 2) x 0); intros a b; cut (0 < 2).
  intro; generalize (Rinv_0_lt_compat 2 H3); intro; fold (/ 2 > 0) in H4;
    apply (b (conj H4 H)).
  lra.
  intros; elim H3; clear H3; intros;
    generalize
      (let (H1, H2) :=
        Rmin_Rgt (Rmin (/ 2) x) (eps * / Rabs (2 * d x0)) (R_dist x1 x0) in
        H1); unfold Rgt; intro; elim (H5 H4); clear H5;
      intros; generalize (let (H1, H2) := Rmin_Rgt (/ 2) x (R_dist x1 x0) in H1);
        unfold Rgt; intro; elim (H7 H5); clear H7;
          intros; clear H4 H5; generalize (H1 x1 (conj H3 H8));
            clear H1; intro; unfold D_x in H3; elim H3; intros;
              generalize (not_eq_sym H5); clear H5; intro H5;
                generalize (Rminus_eq_contra x1 x0 H5); intro; generalize H1;
                  pattern (d x0) at 1;
                    rewrite <- (let (H1, H2) := Rmult_ne (d x0) in H2);
                      rewrite <- (Rinv_l (x1 - x0) H9); unfold R_dist;
                        unfold Rminus at 1; rewrite (Rmult_comm (f x1 - f x0) (/ (x1 - x0)));
                          rewrite (Rmult_comm (/ (x1 - x0) * (x1 - x0)) (d x0));
                            rewrite <- (Ropp_mult_distr_l_reverse (d x0) (/ (x1 - x0) * (x1 - x0)));
                              rewrite (Rmult_comm (- d x0) (/ (x1 - x0) * (x1 - x0)));
                                rewrite (Rmult_assoc (/ (x1 - x0)) (x1 - x0) (- d x0));
                                  rewrite <-
                                    (Rmult_plus_distr_l (/ (x1 - x0)) (f x1 - f x0) ((x1 - x0) * - d x0))
                                    ; rewrite (Rabs_mult (/ (x1 - x0)) (f x1 - f x0 + (x1 - x0) * - d x0));
                                      clear H1; intro;
                                        generalize
                                          (Rmult_lt_compat_l (Rabs (x1 - x0))
                                            (Rabs (/ (x1 - x0)) * Rabs (f x1 - f x0 + (x1 - x0) * - d x0)) eps
                                            (Rabs_pos_lt (x1 - x0) H9) H1);
                                          rewrite <-
                                            (Rmult_assoc (Rabs (x1 - x0)) (Rabs (/ (x1 - x0)))
                                              (Rabs (f x1 - f x0 + (x1 - x0) * - d x0)));
                                            rewrite (Rabs_Rinv (x1 - x0) H9);
                                              rewrite (Rinv_r (Rabs (x1 - x0)) (Rabs_no_R0 (x1 - x0) H9));
                                                rewrite
                                                  (let (H1, H2) := Rmult_ne (Rabs (f x1 - f x0 + (x1 - x0) * - d x0)) in H2)
                                                  ; generalize (Rabs_triang_inv (f x1 - f x0) ((x1 - x0) * d x0));
                                                    intro; rewrite (Rmult_comm (x1 - x0) (- d x0));
                                                      rewrite (Ropp_mult_distr_l_reverse (d x0) (x1 - x0));
                                                        fold (f x1 - f x0 - d x0 * (x1 - x0));
                                                          rewrite (Rmult_comm (x1 - x0) (d x0)) in H10; clear H1;
                                                            intro;
                                                              generalize
                                                                (Rle_lt_trans (Rabs (f x1 - f x0) - Rabs (d x0 * (x1 - x0)))
                                                                  (Rabs (f x1 - f x0 - d x0 * (x1 - x0))) (Rabs (x1 - x0) * eps) H10 H1);
                                                                clear H1; intro;
                                                                  generalize
                                                                    (Rplus_lt_compat_l (Rabs (d x0 * (x1 - x0)))
                                                                      (Rabs (f x1 - f x0) - Rabs (d x0 * (x1 - x0))) (
                                                                        Rabs (x1 - x0) * eps) H1); unfold Rminus at 2;
                                                                    rewrite (Rplus_comm (Rabs (f x1 - f x0)) (- Rabs (d x0 * (x1 - x0))));
                                                                      rewrite <-
                                                                        (Rplus_assoc (Rabs (d x0 * (x1 - x0))) (- Rabs (d x0 * (x1 - x0)))
                                                                          (Rabs (f x1 - f x0))); rewrite (Rplus_opp_r (Rabs (d x0 * (x1 - x0))));
                                                                        rewrite (let (H1, H2) := Rplus_ne (Rabs (f x1 - f x0)) in H2);
                                                                          clear H1; intro; cut (Rabs (d x0 * (x1 - x0)) + Rabs (x1 - x0) * eps < eps).
  intro;
    apply
      (Rlt_trans (Rabs (f x1 - f x0))
        (Rabs (d x0 * (x1 - x0)) + Rabs (x1 - x0) * eps) eps H1 H11).
  clear H1 H5 H3 H10; generalize (Rabs_pos_lt (d x0) H2); intro;
    unfold Rgt in H0;
      generalize (Rmult_lt_compat_l eps (R_dist x1 x0) (/ 2) H0 H7);
        clear H7; intro;
          generalize
            (Rmult_lt_compat_l (Rabs (d x0)) (R_dist x1 x0) (
              eps * / Rabs (2 * d x0)) H1 H6); clear H6; intro;
            rewrite (Rmult_comm eps (R_dist x1 x0)) in H3; unfold R_dist in H3, H5;
              rewrite <- (Rabs_mult (d x0) (x1 - x0)) in H5;
                rewrite (Rabs_mult 2 (d x0)) in H5; cut (Rabs 2 <> 0).
  intro; fold (Rabs (d x0) > 0) in H1;
    rewrite
      (Rinv_mult_distr (Rabs 2) (Rabs (d x0)) H6
        (Rlt_dichotomy_converse (Rabs (d x0)) 0 (or_intror (Rabs (d x0) < 0) H1)))
      in H5;
      rewrite (Rmult_comm (Rabs (d x0)) (eps * (/ Rabs 2 * / Rabs (d x0)))) in H5;
        rewrite <- (Rmult_assoc eps (/ Rabs 2) (/ Rabs (d x0))) in H5;
          rewrite (Rmult_assoc (eps * / Rabs 2) (/ Rabs (d x0)) (Rabs (d x0))) in H5;
            rewrite
              (Rinv_l (Rabs (d x0))
                (Rlt_dichotomy_converse (Rabs (d x0)) 0 (or_intror (Rabs (d x0) < 0) H1)))
              in H5; rewrite (let (H1, H2) := Rmult_ne (eps * / Rabs 2) in H1) in H5;
                cut (Rabs 2 = 2).
  intro; rewrite H7 in H5;
    generalize
      (Rplus_lt_compat (Rabs (d x0 * (x1 - x0))) (eps * / 2)
        (Rabs (x1 - x0) * eps) (eps * / 2) H5 H3); intro;
      rewrite eps2 in H10; assumption.
  unfold Rabs; destruct (Rcase_abs 2) as [Hlt|Hge]; auto.
  cut (0 < 2).
  intro H7; elim (Rlt_asym 0 2 H7 Hlt).
  lra.
  apply Rabs_no_R0.
  discrR.
Qed.

(*********)
Lemma Dconst :
  forall (D:R -> Prop) (y x0:R), D_in (fun x:R => y) (fun x:R => 0) D x0.
Proof.
  unfold D_in; intros; unfold limit1_in;
    unfold limit_in; unfold Rdiv; intros;
      simpl; split with eps; split; auto.
  intros; rewrite (Rminus_diag_eq y y (eq_refl y)); rewrite Rmult_0_l;
    unfold R_dist; rewrite (Rminus_diag_eq 0 0 (eq_refl 0));
      unfold Rabs; case (Rcase_abs 0); intro.
  absurd (0 < 0); auto.
  red; intro; apply (Rlt_irrefl 0 H1).
  unfold Rgt in H0; assumption.
Qed.

(*********)
Lemma Dx :
  forall (D:R -> Prop) (x0:R), D_in (fun x:R => x) (fun x:R => 1) D x0.
Proof.
  unfold D_in; unfold Rdiv; intros; unfold limit1_in;
    unfold limit_in; intros; simpl; split with eps;
      split; auto.
  intros; elim H0; clear H0; intros; unfold D_x in H0; elim H0; intros;
    rewrite (Rinv_r (x - x0) (Rminus_eq_contra x x0 (sym_not_eq H3)));
      unfold R_dist; rewrite (Rminus_diag_eq 1 1 (refl_equal 1));
        unfold Rabs; case (Rcase_abs 0) as [Hlt|Hge].
  absurd (0 < 0); auto.
  red in |- *; intro; apply (Rlt_irrefl 0 Hlt).
  unfold Rgt in H; assumption.
Qed.

(*********)
Lemma Dadd :
  forall (D:R -> Prop) (df dg f g:R -> R) (x0:R),
    D_in f df D x0 ->
    D_in g dg D x0 ->
    D_in (fun x:R => f x + g x) (fun x:R => df x + dg x) D x0.
Proof.
  unfold D_in; intros;
    generalize
      (limit_plus (fun x:R => (f x - f x0) * / (x - x0))
        (fun x:R => (g x - g x0) * / (x - x0)) (D_x D x0) (
          df x0) (dg x0) x0 H H0); clear H H0; unfold limit1_in;
      unfold limit_in; simpl; intros; elim (H eps H0);
        clear H; intros; elim H; clear H; intros; split with x;
          split; auto; intros; generalize (H1 x1 H2); clear H1;
            intro; rewrite (Rmult_comm (f x1 - f x0) (/ (x1 - x0))) in H1;
              rewrite (Rmult_comm (g x1 - g x0) (/ (x1 - x0))) in H1;
                rewrite <- (Rmult_plus_distr_l (/ (x1 - x0)) (f x1 - f x0) (g x1 - g x0))
                  in H1;
                  rewrite (Rmult_comm (/ (x1 - x0)) (f x1 - f x0 + (g x1 - g x0))) in H1;
                    cut (f x1 - f x0 + (g x1 - g x0) = f x1 + g x1 - (f x0 + g x0)).
  intro; rewrite H3 in H1; assumption.
  ring.
Qed.

(*********)
Lemma Dmult :
  forall (D:R -> Prop) (df dg f g:R -> R) (x0:R),
    D_in f df D x0 ->
    D_in g dg D x0 ->
    D_in (fun x:R => f x * g x) (fun x:R => df x * g x + f x * dg x) D x0.
Proof.
  intros; unfold D_in; generalize H H0; intros; unfold D_in in H, H0;
    generalize (cont_deriv f df D x0 H1); unfold continue_in;
      intro;
        generalize
          (limit_mul (fun x:R => (g x - g x0) * / (x - x0)) (
            fun x:R => f x) (D_x D x0) (dg x0) (f x0) x0 H0 H3);
          intro; cut (limit1_in (fun x:R => g x0) (D_x D x0) (g x0) x0).
  intro;
    generalize
      (limit_mul (fun x:R => (f x - f x0) * / (x - x0)) (
        fun _:R => g x0) (D_x D x0) (df x0) (g x0) x0 H H5);
      clear H H0 H1 H2 H3 H5; intro;
        generalize
          (limit_plus (fun x:R => (f x - f x0) * / (x - x0) * g x0)
            (fun x:R => (g x - g x0) * / (x - x0) * f x) (
              D_x D x0) (df x0 * g x0) (dg x0 * f x0) x0 H H4);
          clear H4 H; intro; unfold limit1_in in H; unfold limit_in in H;
            simpl in H; unfold limit1_in; unfold limit_in;
              simpl; intros; elim (H eps H0); clear H; intros;
                elim H; clear H; intros; split with x; split; auto;
                  intros; generalize (H1 x1 H2); clear H1; intro;
                    rewrite (Rmult_comm (f x1 - f x0) (/ (x1 - x0))) in H1;
                      rewrite (Rmult_comm (g x1 - g x0) (/ (x1 - x0))) in H1;
                        rewrite (Rmult_assoc (/ (x1 - x0)) (f x1 - f x0) (g x0)) in H1;
                          rewrite (Rmult_assoc (/ (x1 - x0)) (g x1 - g x0) (f x1)) in H1;
                            rewrite <-
                              (Rmult_plus_distr_l (/ (x1 - x0)) ((f x1 - f x0) * g x0)
                                ((g x1 - g x0) * f x1)) in H1;
                              rewrite
                                (Rmult_comm (/ (x1 - x0)) ((f x1 - f x0) * g x0 + (g x1 - g x0) * f x1))
                                in H1; rewrite (Rmult_comm (dg x0) (f x0)) in H1;
                                  cut
                                    ((f x1 - f x0) * g x0 + (g x1 - g x0) * f x1 = f x1 * g x1 - f x0 * g x0).
  intro; rewrite H3 in H1; assumption.
  ring.
  unfold limit1_in; unfold limit_in; simpl; intros;
    split with eps; split; auto; intros; elim (R_dist_refl (g x0) (g x0));
      intros a b; rewrite (b (eq_refl (g x0))); unfold Rgt in H;
        assumption.
Qed.

(*********)
Lemma Dmult_const :
  forall (D:R -> Prop) (f df:R -> R) (x0 a:R),
    D_in f df D x0 -> D_in (fun x:R => a * f x) (fun x:R => a * df x) D x0.
Proof.
  intros;
    generalize (Dmult D (fun _:R => 0) df (fun _:R => a) f x0 (Dconst D a x0) H);
      unfold D_in; intros; rewrite (Rmult_0_l (f x0)) in H0;
        rewrite (let (H1, H2) := Rplus_ne (a * df x0) in H2) in H0;
          assumption.
Qed.

(*********)
Lemma Dopp :
  forall (D:R -> Prop) (f df:R -> R) (x0:R),
    D_in f df D x0 -> D_in (fun x:R => - f x) (fun x:R => - df x) D x0.
Proof.
  intros; generalize (Dmult_const D f df x0 (-1) H); unfold D_in;
    unfold limit1_in; unfold limit_in;
      intros; generalize (H0 eps H1); clear H0; intro; elim H0;
        clear H0; intros; elim H0; clear H0; simpl;
          intros; split with x; split; auto.
  intros; generalize (H2 x1 H3); clear H2; intro.
  replace (- f x1 - - f x0) with (-1 * f x1 - -1 * f x0) by ring.
  replace (- df x0) with (-1 * df x0) by ring.
  exact H2.
Qed.

(*********)
Lemma Dminus :
  forall (D:R -> Prop) (df dg f g:R -> R) (x0:R),
    D_in f df D x0 ->
    D_in g dg D x0 ->
    D_in (fun x:R => f x - g x) (fun x:R => df x - dg x) D x0.
Proof.
  unfold Rminus; intros; generalize (Dopp D g dg x0 H0); intro;
    apply (Dadd D df (fun x:R => - dg x) f (fun x:R => - g x) x0);
      assumption.
Qed.

(*********)
Lemma Dx_pow_n :
  forall (n:nat) (D:R -> Prop) (x0:R),
    D_in (fun x:R => x ^ n) (fun x:R => INR n * x ^ (n - 1)) D x0.
Proof.
  simple induction n; intros.
  simpl; rewrite Rmult_0_l; apply Dconst.
  intros; cut (n0 = (S n0 - 1)%nat);
    [ intro a; rewrite <- a; clear a | simpl; apply minus_n_O ].
  generalize
    (Dmult D (fun _:R => 1) (fun x:R => INR n0 * x ^ (n0 - 1)) (
      fun x:R => x) (fun x:R => x ^ n0) x0 (Dx D x0) (
        H D x0)); unfold D_in; unfold limit1_in;
    unfold limit_in; simpl; intros; elim (H0 eps H1);
      clear H0; intros; elim H0; clear H0; intros; split with x;
        split; auto.
  intros; generalize (H2 x1 H3); clear H2 H3; intro;
    rewrite (let (H1, H2) := Rmult_ne (x0 ^ n0) in H2) in H2;
      rewrite (tech_pow_Rmult x1 n0) in H2; rewrite (tech_pow_Rmult x0 n0) in H2;
        rewrite (Rmult_comm (INR n0) (x0 ^ (n0 - 1))) in H2;
          rewrite <- (Rmult_assoc x0 (x0 ^ (n0 - 1)) (INR n0)) in H2;
            rewrite (tech_pow_Rmult x0 (n0 - 1)) in H2; elim (Peano_dec.eq_nat_dec n0 0) ; intros cond.
  rewrite cond in H2; rewrite cond; simpl in H2; simpl;
    cut (1 + x0 * 1 * 0 = 1 * 1);
      [ intro A; rewrite A in H2; assumption | ring ].
  cut (n0 <> 0%nat -> S (n0 - 1) = n0); [ intro | omega ];
    rewrite (H3 cond) in H2; rewrite (Rmult_comm (x0 ^ n0) (INR n0)) in H2;
      rewrite (tech_pow_Rplus x0 n0 n0) in H2; assumption.
Qed.

(*********)
Lemma Dcomp :
  forall (Df Dg:R -> Prop) (df dg f g:R -> R) (x0:R),
    D_in f df Df x0 ->
    D_in g dg Dg (f x0) ->
    D_in (fun x:R => g (f x)) (fun x:R => df x * dg (f x)) (Dgf Df Dg f) x0.
Proof.
  intros Df Dg df dg f g x0 H H0; generalize H H0; unfold D_in;
    unfold Rdiv; intros;
      generalize
        (limit_comp f (fun x:R => (g x - g (f x0)) * / (x - f x0)) (
          D_x Df x0) (D_x Dg (f x0)) (f x0) (dg (f x0)) x0);
        intro; generalize (cont_deriv f df Df x0 H); intro;
          unfold continue_in in H4; generalize (H3 H4 H2); clear H3;
            intro;
              generalize
                (limit_mul (fun x:R => (g (f x) - g (f x0)) * / (f x - f x0))
                  (fun x:R => (f x - f x0) * / (x - x0))
                  (Dgf (D_x Df x0) (D_x Dg (f x0)) f) (dg (f x0)) (
                    df x0) x0 H3); intro;
                cut
                  (limit1_in (fun x:R => (f x - f x0) * / (x - x0))
                    (Dgf (D_x Df x0) (D_x Dg (f x0)) f) (df x0) x0).
  intro; generalize (H5 H6); clear H5; intro;
    generalize
      (limit_mul (fun x:R => (f x - f x0) * / (x - x0)) (
        fun x:R => dg (f x0)) (D_x Df x0) (df x0) (dg (f x0)) x0 H1
      (limit_free (fun x:R => dg (f x0)) (D_x Df x0) x0 x0));
      intro; unfold limit1_in; unfold limit_in;
        simpl; unfold limit1_in in H5, H7; unfold limit_in in H5, H7;
          simpl in H5, H7; intros; elim (H5 eps H8); elim (H7 eps H8);
            clear H5 H7; intros; elim H5; elim H7; clear H5 H7;
              intros; split with (Rmin x x1); split.
  elim (Rmin_Rgt x x1 0); intros a b; apply (b (conj H9 H5)); clear a b.
  intros; elim H11; clear H11; intros; elim (Rmin_Rgt x x1 (R_dist x2 x0));
    intros a b; clear b; unfold Rgt in a; elim (a H12);
      clear H5 a; intros; unfold D_x, Dgf in H11, H7, H10;
        clear H12; elim (Req_dec (f x2) (f x0)); intro.
  elim H11; clear H11; intros; elim H11; clear H11; intros;
    generalize (H10 x2 (conj (conj H11 H14) H5)); intro;
      rewrite (Rminus_diag_eq (f x2) (f x0) H12) in H16;
        rewrite (Rmult_0_l (/ (x2 - x0))) in H16;
          rewrite (Rmult_0_l (dg (f x0))) in H16; rewrite H12;
            rewrite (Rminus_diag_eq (g (f x0)) (g (f x0)) (eq_refl (g (f x0))));
              rewrite (Rmult_0_l (/ (x2 - x0))); assumption.
  clear H10 H5; elim H11; clear H11; intros; elim H5; clear H5; intros;
    cut
      (((Df x2 /\ x0 <> x2) /\ Dg (f x2) /\ f x0 <> f x2) /\ R_dist x2 x0 < x1);
      auto; intro; generalize (H7 x2 H14); intro;
        generalize (Rminus_eq_contra (f x2) (f x0) H12); intro;
          rewrite
            (Rmult_assoc (g (f x2) - g (f x0)) (/ (f x2 - f x0))
              ((f x2 - f x0) * / (x2 - x0))) in H15;
            rewrite <- (Rmult_assoc (/ (f x2 - f x0)) (f x2 - f x0) (/ (x2 - x0)))
              in H15; rewrite (Rinv_l (f x2 - f x0) H16) in H15;
                rewrite (let (H1, H2) := Rmult_ne (/ (x2 - x0)) in H2) in H15;
                  rewrite (Rmult_comm (df x0) (dg (f x0))); assumption.
  clear H5 H3 H4 H2; unfold limit1_in; unfold limit_in;
    simpl; unfold limit1_in in H1; unfold limit_in in H1;
      simpl in H1; intros; elim (H1 eps H2); clear H1; intros;
        elim H1; clear H1; intros; split with x; split; auto;
          intros; unfold D_x, Dgf in H4, H3; elim H4; clear H4;
            intros; elim H4; clear H4; intros; exact (H3 x1 (conj H4 H5)).
Qed.

(*********)
Lemma D_pow_n :
  forall (n:nat) (D:R -> Prop) (x0:R) (expr dexpr:R -> R),
    D_in expr dexpr D x0 ->
    D_in (fun x:R => expr x ^ n)
    (fun x:R => INR n * expr x ^ (n - 1) * dexpr x) (
      Dgf D D expr) x0.
Proof.
  intros n D x0 expr dexpr H;
    generalize
      (Dcomp D D dexpr (fun x:R => INR n * x ^ (n - 1)) expr (
        fun x:R => x ^ n) x0 H (Dx_pow_n n D (expr x0)));
      intro; unfold D_in; unfold limit1_in;
        unfold limit_in; simpl; intros; unfold D_in in H0;
          unfold limit1_in in H0; unfold limit_in in H0; simpl in H0;
            elim (H0 eps H1); clear H0; intros; elim H0; clear H0;
              intros; split with x; split; intros; auto.
  cut
    (dexpr x0 * (INR n * expr x0 ^ (n - 1)) =
      INR n * expr x0 ^ (n - 1) * dexpr x0);
    [ intro Rew; rewrite <- Rew; exact (H2 x1 H3) | ring ].
Qed.
