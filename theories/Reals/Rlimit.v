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
(**          Definition of the limit                     *)
(*                                                       *)
(*********************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import Lra.
Local Open Scope R_scope.

(*******************************)
(** *   Calculus               *)
(*******************************)
(*********)
Lemma eps2_Rgt_R0 : forall eps:R, eps > 0 -> eps * / 2 > 0.
Proof.
  intros; lra.
Qed.

(*********)
Lemma eps2 : forall eps:R, eps * / 2 + eps * / 2 = eps.
Proof.
  intro esp.
  apply eq_sym, double_var.
Qed.

(*********)
Lemma eps4 : forall eps:R, eps * / (2 + 2) + eps * / (2 + 2) = eps * / 2.
Proof.
  intro eps.
  field.
Qed.

(*********)
Lemma Rlt_eps2_eps : forall eps:R, eps > 0 -> eps * / 2 < eps.
Proof.
  intros.
  lra.
Qed.

(*********)
Lemma Rlt_eps4_eps : forall eps:R, eps > 0 -> eps * / (2 + 2) < eps.
Proof.
  intros.
  lra.
Qed.

(*********)
Lemma prop_eps : forall r:R, (forall eps:R, eps > 0 -> r < eps) -> r <= 0.
Proof.
  intros; elim (Rtotal_order r 0); intro.
  apply Rlt_le; assumption.
  elim H0; intro.
  apply Req_le; assumption.
  clear H0; generalize (H r H1); intro; generalize (Rlt_irrefl r); intro;
    exfalso; auto.
Qed.

(*********)
Definition mul_factor (l l':R) := / (1 + (Rabs l + Rabs l')).

(*********)
Lemma mul_factor_wd : forall l l':R, 1 + (Rabs l + Rabs l') <> 0.
Proof.
  intros; rewrite (Rplus_comm 1 (Rabs l + Rabs l')); apply tech_Rplus.
  cut (Rabs (l + l') <= Rabs l + Rabs l').
  cut (0 <= Rabs (l + l')).
  exact (Rle_trans _ _ _).
  exact (Rabs_pos (l + l')).
  exact (Rabs_triang _ _).
  exact Rlt_0_1.
Qed.

(*********)
Lemma mul_factor_gt : forall eps l l':R, eps > 0 -> eps * mul_factor l l' > 0.
Proof.
  intros; unfold Rgt; rewrite <- (Rmult_0_r eps);
    apply Rmult_lt_compat_l.
  assumption.
  unfold mul_factor; apply Rinv_0_lt_compat;
    cut (1 <= 1 + (Rabs l + Rabs l')).
  cut (0 < 1).
  exact (Rlt_le_trans _ _ _).
  exact Rlt_0_1.
  replace (1 <= 1 + (Rabs l + Rabs l')) with (1 + 0 <= 1 + (Rabs l + Rabs l')).
  apply Rplus_le_compat_l.
  cut (Rabs (l + l') <= Rabs l + Rabs l').
  cut (0 <= Rabs (l + l')).
  exact (Rle_trans _ _ _).
  exact (Rabs_pos _).
  exact (Rabs_triang _ _).
  rewrite (proj1 (Rplus_ne 1)); trivial.
Qed.

(*********)
Lemma mul_factor_gt_f :
  forall eps l l':R, eps > 0 -> Rmin 1 (eps * mul_factor l l') > 0.
  intros; apply Rmin_Rgt_r; split.
  exact Rlt_0_1.
  exact (mul_factor_gt eps l l' H).
Qed.


(*******************************)
(** *   Metric space           *)
(*******************************)

(*********)
Record Metric_Space : Type :=
  {Base : Type;
    dist : Base -> Base -> R;
    dist_pos : forall x y:Base, dist x y >= 0;
    dist_sym : forall x y:Base, dist x y = dist y x;
    dist_refl : forall x y:Base, dist x y = 0 <-> x = y;
    dist_tri : forall x y z:Base, dist x y <= dist x z + dist z y}.

(*******************************)
(** ** Limit in Metric space   *)
(*******************************)

(*********)
Definition limit_in (X X':Metric_Space) (f:Base X -> Base X')
  (D:Base X -> Prop) (x0:Base X) (l:Base X') :=
  forall eps:R,
    eps > 0 ->
    exists alp : R,
      alp > 0 /\
      (forall x:Base X, D x /\ X.(dist) x x0 < alp -> X'.(dist) (f x) l < eps).

(*******************************)
(** **  R is a metric space    *)
(*******************************)

(*********)
Definition R_met : Metric_Space :=
  Build_Metric_Space R R_dist R_dist_pos R_dist_sym R_dist_refl R_dist_tri.

Declare Equivalent Keys dist R_dist.

(*******************************)
(** *      Limit 1 arg         *)
(*******************************)
(*********)
Definition Dgf (Df Dg:R -> Prop) (f:R -> R) (x:R) := Df x /\ Dg (f x).

(*********)
Definition limit1_in (f:R -> R) (D:R -> Prop) (l x0:R) : Prop :=
  limit_in R_met R_met f D x0 l.

(*********)
Lemma tech_limit :
  forall (f:R -> R) (D:R -> Prop) (l x0:R),
    D x0 -> limit1_in f D l x0 -> l = f x0.
Proof.
  intros f D l x0 H H0.
  case (Rabs_pos (f x0 - l)); intros H1.
  absurd (R_met.(@dist) (f x0) l < R_met.(@dist) (f x0) l).
  apply Rlt_irrefl.
  case (H0 (R_met.(@dist) (f x0) l)); auto.
  intros alpha1 [H2 H3]; apply H3; auto; split; auto.
  case (dist_refl R_met x0 x0); intros Hr1 Hr2; rewrite Hr2; auto.
  case (dist_refl R_met (f x0) l); intros Hr1 Hr2; symmetry; auto.
Qed.

(*********)
Lemma tech_limit_contr :
  forall (f:R -> R) (D:R -> Prop) (l x0:R),
    D x0 -> l <> f x0 -> ~ limit1_in f D l x0.
Proof.
  intros; generalize (tech_limit f D l x0); tauto.
Qed.

(*********)
Lemma lim_x : forall (D:R -> Prop) (x0:R), limit1_in (fun x:R => x) D x0 x0.
Proof.
  unfold limit1_in; unfold limit_in; simpl; intros;
    split with eps; split; auto; intros; elim H0; intros;
      auto.
Qed.

(*********)
Lemma limit_plus :
  forall (f g:R -> R) (D:R -> Prop) (l l' x0:R),
    limit1_in f D l x0 ->
    limit1_in g D l' x0 -> limit1_in (fun x:R => f x + g x) D (l + l') x0.
Proof.
  intros; unfold limit1_in; unfold limit_in; simpl;
    intros; elim (H (eps * / 2) (eps2_Rgt_R0 eps H1));
      elim (H0 (eps * / 2) (eps2_Rgt_R0 eps H1)); simpl;
        clear H H0; intros; elim H; elim H0; clear H H0; intros;
          split with (Rmin x1 x); split.
  exact (Rmin_Rgt_r x1 x 0 (conj H H2)).
  intros; elim H4; clear H4; intros;
    cut (R_dist (f x2) l + R_dist (g x2) l' < eps).
  cut (R_dist (f x2 + g x2) (l + l') <= R_dist (f x2) l + R_dist (g x2) l').
  exact (Rle_lt_trans _ _ _).
  exact (R_dist_plus _ _ _ _).
  elim (Rmin_Rgt_l x1 x (R_dist x2 x0) H5); clear H5; intros.
  generalize (H3 x2 (conj H4 H6)); generalize (H0 x2 (conj H4 H5)); intros;
    replace eps with (eps * / 2 + eps * / 2).
  exact (Rplus_lt_compat _ _ _ _ H7 H8).
  exact (eps2 eps).
Qed.

(*********)
Lemma limit_Ropp :
  forall (f:R -> R) (D:R -> Prop) (l x0:R),
    limit1_in f D l x0 -> limit1_in (fun x:R => - f x) D (- l) x0.
Proof.
  unfold limit1_in; unfold limit_in; simpl; intros;
    elim (H eps H0); clear H; intros; elim H; clear H;
      intros; split with x; split; auto; intros; generalize (H1 x1 H2);
        clear H1; intro; unfold R_dist; unfold Rminus;
          rewrite (Ropp_involutive l); rewrite (Rplus_comm (- f x1) l);
            fold (l - f x1); fold (R_dist l (f x1));
              rewrite R_dist_sym; assumption.
Qed.

(*********)
Lemma limit_minus :
  forall (f g:R -> R) (D:R -> Prop) (l l' x0:R),
    limit1_in f D l x0 ->
    limit1_in g D l' x0 -> limit1_in (fun x:R => f x - g x) D (l - l') x0.
Proof.
  intros; unfold Rminus; generalize (limit_Ropp g D l' x0 H0); intro;
    exact (limit_plus f (fun x:R => - g x) D l (- l') x0 H H1).
Qed.

(*********)
Lemma limit_free :
  forall (f:R -> R) (D:R -> Prop) (x x0:R),
    limit1_in (fun h:R => f x) D (f x) x0.
Proof.
  unfold limit1_in; unfold limit_in; simpl; intros;
    split with eps; split; auto; intros; elim (R_dist_refl (f x) (f x));
      intros a b; rewrite (b (eq_refl (f x))); unfold Rgt in H;
        assumption.
Qed.

(*********)
Lemma limit_mul :
  forall (f g:R -> R) (D:R -> Prop) (l l' x0:R),
    limit1_in f D l x0 ->
    limit1_in g D l' x0 -> limit1_in (fun x:R => f x * g x) D (l * l') x0.
Proof.
  intros; unfold limit1_in; unfold limit_in; simpl;
    intros;
      elim (H (Rmin 1 (eps * mul_factor l l')) (mul_factor_gt_f eps l l' H1));
        elim (H0 (eps * mul_factor l l') (mul_factor_gt eps l l' H1));
          clear H H0; simpl; intros; elim H; elim H0;
            clear H H0; intros; split with (Rmin x1 x); split.
  exact (Rmin_Rgt_r x1 x 0 (conj H H2)).
  intros; elim H4; clear H4; intros; unfold R_dist;
    replace (f x2 * g x2 - l * l') with (f x2 * (g x2 - l') + l' * (f x2 - l)).
  cut (Rabs (f x2 * (g x2 - l')) + Rabs (l' * (f x2 - l)) < eps).
  cut
    (Rabs (f x2 * (g x2 - l') + l' * (f x2 - l)) <=
      Rabs (f x2 * (g x2 - l')) + Rabs (l' * (f x2 - l))).
  exact (Rle_lt_trans _ _ _).
  exact (Rabs_triang _ _).
  rewrite (Rabs_mult (f x2) (g x2 - l')); rewrite (Rabs_mult l' (f x2 - l));
    cut
      ((1 + Rabs l) * (eps * mul_factor l l') + Rabs l' * (eps * mul_factor l l') <=
        eps).
  cut
    (Rabs (f x2) * Rabs (g x2 - l') + Rabs l' * Rabs (f x2 - l) <
      (1 + Rabs l) * (eps * mul_factor l l') + Rabs l' * (eps * mul_factor l l')).
  exact (Rlt_le_trans _ _ _).
  elim (Rmin_Rgt_l x1 x (R_dist x2 x0) H5); clear H5; intros;
    generalize (H0 x2 (conj H4 H5)); intro; generalize (Rmin_Rgt_l _ _ _ H7);
      intro; elim H8; intros; clear H0 H8; apply Rplus_lt_le_compat.
  apply Rmult_ge_0_gt_0_lt_compat.
  apply Rle_ge.
  exact (Rabs_pos (g x2 - l')).
  rewrite (Rplus_comm 1 (Rabs l)); unfold Rgt; apply Rle_lt_0_plus_1;
    exact (Rabs_pos l).
  unfold R_dist in H9;
    apply (Rplus_lt_reg_l (- Rabs l) (Rabs (f x2)) (1 + Rabs l)).
  rewrite <- (Rplus_assoc (- Rabs l) 1 (Rabs l));
    rewrite (Rplus_comm (- Rabs l) 1);
      rewrite (Rplus_assoc 1 (- Rabs l) (Rabs l)); rewrite (Rplus_opp_l (Rabs l));
        rewrite (proj1 (Rplus_ne 1)); rewrite (Rplus_comm (- Rabs l) (Rabs (f x2)));
          generalize H9; cut (Rabs (f x2) - Rabs l <= Rabs (f x2 - l)).
  exact (Rle_lt_trans _ _ _).
  exact (Rabs_triang_inv _ _).
  generalize (H3 x2 (conj H4 H6)); trivial.
  apply Rmult_le_compat_l.
  exact (Rabs_pos l').
  unfold Rle; left; assumption.
  rewrite (Rmult_comm (1 + Rabs l) (eps * mul_factor l l'));
    rewrite (Rmult_comm (Rabs l') (eps * mul_factor l l'));
      rewrite <-
        (Rmult_plus_distr_l (eps * mul_factor l l') (1 + Rabs l) (Rabs l'))
        ; rewrite (Rmult_assoc eps (mul_factor l l') (1 + Rabs l + Rabs l'));
          rewrite (Rplus_assoc 1 (Rabs l) (Rabs l')); unfold mul_factor;
            rewrite (Rinv_l (1 + (Rabs l + Rabs l')) (mul_factor_wd l l'));
              rewrite (proj1 (Rmult_ne eps)); apply Req_le; trivial.
  ring.
Qed.

(*********)
Definition adhDa (D:R -> Prop) (a:R) : Prop :=
  forall alp:R, alp > 0 ->  exists x : R, D x /\ R_dist x a < alp.

(*********)
Lemma single_limit :
  forall (f:R -> R) (D:R -> Prop) (l l' x0:R),
    adhDa D x0 -> limit1_in f D l x0 -> limit1_in f D l' x0 -> l = l'.
Proof.
  unfold limit1_in; unfold limit_in; intros.
  simpl in *.
  cut (forall eps:R, eps > 0 -> dist R_met l l' < 2 * eps).
  clear H0 H1; unfold dist in |- *; unfold R_met; unfold R_dist in |- *;
    unfold Rabs; case (Rcase_abs (l - l')) as [Hlt|Hge]; intros.
  cut (forall eps:R, eps > 0 -> - (l - l') < eps).
  intro; generalize (prop_eps (- (l - l')) H1); intro;
    generalize (Ropp_gt_lt_0_contravar (l - l') Hlt); intro;
      unfold Rgt in H3; generalize (Rgt_not_le (- (l - l')) 0 H3);
        intro; exfalso; auto.
  intros; cut (eps * / 2 > 0).
  intro; generalize (H0 (eps * / 2) H2); rewrite (Rmult_comm eps (/ 2));
    rewrite <- (Rmult_assoc 2 (/ 2) eps); rewrite (Rinv_r 2).
  elim (Rmult_ne eps); intros a b; rewrite b; clear a b; trivial. 
  apply (Rlt_dichotomy_converse 2 0); right; generalize Rlt_0_1; intro;
    unfold Rgt; generalize (Rplus_lt_compat_l 1 0 1 H3);
      intro; elim (Rplus_ne 1); intros a b; rewrite a in H4;
        clear a b; apply (Rlt_trans 0 1 2 H3 H4).
  unfold Rgt; unfold Rgt in H1; rewrite (Rmult_comm eps (/ 2));
    rewrite <- (Rmult_0_r (/ 2)); apply (Rmult_lt_compat_l (/ 2) 0 eps);
      auto.
  apply (Rinv_0_lt_compat 2); cut (1 < 2).
  intro; apply (Rlt_trans 0 1 2 Rlt_0_1 H2).
  generalize (Rplus_lt_compat_l 1 0 1 Rlt_0_1); elim (Rplus_ne 1); intros a b;
    rewrite a; clear a b; trivial.
(**)
  cut (forall eps:R, eps > 0 -> l - l' < eps).
  intro; generalize (prop_eps (l - l') H1); intro; elim (Rle_le_eq (l - l') 0);
    intros a b; clear b; apply (Rminus_diag_uniq l l');
      apply a; split.
  assumption.
  apply (Rge_le (l - l') 0 Hge).
  intros; cut (eps * / 2 > 0).
  intro; generalize (H0 (eps * / 2) H2); rewrite (Rmult_comm eps (/ 2));
    rewrite <- (Rmult_assoc 2 (/ 2) eps); rewrite (Rinv_r 2).
  elim (Rmult_ne eps); intros a b; rewrite b; clear a b; trivial.
  apply (Rlt_dichotomy_converse 2 0); right; generalize Rlt_0_1; intro;
    unfold Rgt; generalize (Rplus_lt_compat_l 1 0 1 H3);
      intro; elim (Rplus_ne 1); intros a b; rewrite a in H4;
        clear a b; apply (Rlt_trans 0 1 2 H3 H4).
  unfold Rgt; unfold Rgt in H1; rewrite (Rmult_comm eps (/ 2));
    rewrite <- (Rmult_0_r (/ 2)); apply (Rmult_lt_compat_l (/ 2) 0 eps);
      auto.
  apply (Rinv_0_lt_compat 2); cut (1 < 2).
  intro; apply (Rlt_trans 0 1 2 Rlt_0_1 H2).
  generalize (Rplus_lt_compat_l 1 0 1 Rlt_0_1); elim (Rplus_ne 1); intros a b;
    rewrite a; clear a b; trivial.
(**)
  intros; unfold adhDa in H; elim (H0 eps H2); intros; elim (H1 eps H2); intros;
    clear H0 H1; elim H3; elim H4; clear H3 H4; intros;
      simpl; simpl in H1, H4; generalize (Rmin_Rgt x x1 0);
        intro; elim H5; intros; clear H5; elim (H (Rmin x x1) (H7 (conj H3 H0)));
          intros; elim H5; intros; clear H5 H H6 H7;
            generalize (Rmin_Rgt x x1 (R_dist x2 x0)); intro;
              elim H; intros; clear H H6; unfold Rgt in H5; elim (H5 H9);
                intros; clear H5 H9; generalize (H1 x2 (conj H8 H6));
                  generalize (H4 x2 (conj H8 H)); clear H8 H H6 H1 H4 H0 H3;
                    intros;
                      generalize
                        (Rplus_lt_compat (R_dist (f x2) l) eps (R_dist (f x2) l') eps H H0);
                        unfold R_dist; intros; rewrite (Rabs_minus_sym (f x2) l) in H1;
                          rewrite (Rmult_comm 2 eps); replace (eps *2) with (eps + eps) by ring;
                              generalize (R_dist_tri l l' (f x2)); unfold R_dist;
                                intros;
                                  apply
                                    (Rle_lt_trans (Rabs (l - l')) (Rabs (l - f x2) + Rabs (f x2 - l'))
                                      (eps + eps) H3 H1).
Qed.

(*********)
Lemma limit_comp :
  forall (f g:R -> R) (Df Dg:R -> Prop) (l l' x0:R),
    limit1_in f Df l x0 ->
    limit1_in g Dg l' l -> limit1_in (fun x:R => g (f x)) (Dgf Df Dg f) l' x0.
Proof.
  unfold limit1_in, limit_in, Dgf; simpl.
  intros f g Df Dg l l' x0 Hf Hg eps eps_pos.
  elim (Hg eps eps_pos).
  intros alpg lg.
  elim (Hf alpg).
  2: tauto.
  intros alpf lf.
  exists alpf.
  intuition.
Qed.

(*********)

Lemma limit_inv :
  forall (f:R -> R) (D:R -> Prop) (l x0:R),
    limit1_in f D l x0 -> l <> 0 -> limit1_in (fun x:R => / f x) D (/ l) x0.
Proof.
  unfold limit1_in; unfold limit_in; simpl;
    unfold R_dist; intros; elim (H (Rabs l / 2)).
  intros delta1 H2; elim (H (eps * (Rsqr l / 2))).
  intros delta2 H3; elim H2; elim H3; intros; exists (Rmin delta1 delta2);
    split.
  unfold Rmin; case (Rle_dec delta1 delta2); intro; assumption.
  intro; generalize (H5 x); clear H5; intro H5; generalize (H7 x); clear H7;
    intro H7; intro H10; elim H10; intros; cut (D x /\ Rabs (x - x0) < delta1).
  cut (D x /\ Rabs (x - x0) < delta2).
  intros; generalize (H5 H11); clear H5; intro H5; generalize (H7 H12);
    clear H7; intro H7; generalize (Rabs_triang_inv l (f x));
      intro; rewrite Rabs_minus_sym in H7;
        generalize
          (Rle_lt_trans (Rabs l - Rabs (f x)) (Rabs (l - f x)) (Rabs l / 2) H13 H7);
          intro;
            generalize
              (Rplus_lt_compat_l (Rabs (f x) - Rabs l / 2) (Rabs l - Rabs (f x))
                (Rabs l / 2) H14);
              replace (Rabs (f x) - Rabs l / 2 + (Rabs l - Rabs (f x))) with (Rabs l / 2).
  unfold Rminus; rewrite Rplus_assoc; rewrite Rplus_opp_l;
    rewrite Rplus_0_r; intro; cut (f x <> 0).
  intro; replace (/ f x + - / l) with ((l - f x) * / (l * f x)).
  rewrite Rabs_mult; rewrite Rabs_Rinv.
  cut (/ Rabs (l * f x) < 2 / Rsqr l).
  intro; rewrite Rabs_minus_sym in H5; cut (0 <= / Rabs (l * f x)).
  intro;
    generalize
      (Rmult_le_0_lt_compat (Rabs (l - f x)) (eps * (Rsqr l / 2))
        (/ Rabs (l * f x)) (2 / Rsqr l) (Rabs_pos (l - f x)) H18 H5 H17);
      replace (eps * (Rsqr l / 2) * (2 / Rsqr l)) with eps.
  intro; assumption.
  unfold Rdiv; unfold Rsqr; rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm l).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm l).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; reflexivity.
  discrR.
  exact H0.
  exact H0.
  exact H0.
  exact H0.
  left; apply Rinv_0_lt_compat; apply Rabs_pos_lt; apply prod_neq_R0;
    assumption.
  rewrite Rmult_comm; rewrite Rabs_mult; rewrite Rinv_mult_distr.
  rewrite (Rsqr_abs l); unfold Rsqr; unfold Rdiv;
    rewrite Rinv_mult_distr.
  repeat rewrite <- Rmult_assoc; apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  apply Rmult_lt_reg_l with (Rabs (f x) * Rabs l * / 2).
  repeat apply Rmult_lt_0_compat.
  apply Rabs_pos_lt; assumption.
  apply Rabs_pos_lt; assumption.
  apply Rinv_0_lt_compat; cut (0%nat <> 2%nat);
    [ intro H17; generalize (lt_INR_0 2 (neq_O_lt 2 H17)); unfold INR;
      intro H18; assumption
      | discriminate ].
  replace (Rabs (f x) * Rabs l * / 2 * / Rabs (f x)) with (Rabs l / 2).
  replace (Rabs (f x) * Rabs l * / 2 * (2 * / Rabs l)) with (Rabs (f x)).
  assumption.
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (Rabs l)).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; reflexivity.
  discrR.
  apply Rabs_no_R0.
  assumption.
  unfold Rdiv.
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (Rabs (f x))).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  reflexivity.
  apply Rabs_no_R0; assumption.
  apply Rabs_no_R0; assumption.
  apply Rabs_no_R0; assumption.
  apply Rabs_no_R0; assumption.
  apply Rabs_no_R0; assumption.
  apply prod_neq_R0; assumption.
  rewrite (Rinv_mult_distr _ _ H0 H16).
  unfold Rminus; rewrite Rmult_plus_distr_r.
  rewrite <- Rmult_assoc.
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l.
  rewrite Ropp_mult_distr_l_reverse.
  rewrite (Rmult_comm (f x)).
  rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  reflexivity.
  assumption.
  assumption.
  red; intro; rewrite H16 in H15; rewrite Rabs_R0 in H15;
    cut (0 < Rabs l / 2).
  intro; elim (Rlt_irrefl 0 (Rlt_trans 0 (Rabs l / 2) 0 H17 H15)).
  unfold Rdiv; apply Rmult_lt_0_compat.
  apply Rabs_pos_lt; assumption.
  apply Rinv_0_lt_compat; cut (0%nat <> 2%nat);
    [ intro H17; generalize (lt_INR_0 2 (neq_O_lt 2 H17)); unfold INR;
      intro; assumption
      | discriminate ].
  pattern (Rabs l) at 3; rewrite double_var.
  ring.
  split;
    [ assumption
      | apply Rlt_le_trans with (Rmin delta1 delta2);
        [ assumption | apply Rmin_r ] ].
  split;
    [ assumption
      | apply Rlt_le_trans with (Rmin delta1 delta2);
        [ assumption | apply Rmin_l ] ].
  change (0 < eps * (Rsqr l / 2)); unfold Rdiv;
    repeat rewrite Rmult_assoc; apply Rmult_lt_0_compat.
  assumption.
  apply Rmult_lt_0_compat. apply Rsqr_pos_lt; assumption.
  apply Rinv_0_lt_compat; cut (0%nat <> 2%nat);
    [ intro H3; generalize (lt_INR_0 2 (neq_O_lt 2 H3)); unfold INR;
      intro; assumption
      | discriminate ].
  change (0 < Rabs l / 2); unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply Rabs_pos_lt; assumption
      | apply Rinv_0_lt_compat; cut (0%nat <> 2%nat);
        [ intro H3; generalize (lt_INR_0 2 (neq_O_lt 2 H3)); unfold INR;
          intro; assumption
          | discriminate ] ].
Qed.
