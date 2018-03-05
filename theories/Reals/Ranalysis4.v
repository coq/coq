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
Require Import SeqSeries.
Require Import Rtrigo1.
Require Import Ranalysis1.
Require Import Ranalysis3.
Require Import Exp_prop.
Require Import MVT.
Local Open Scope R_scope.

(**********)
Lemma derivable_pt_inv :
  forall (f:R -> R) (x:R),
    f x <> 0 -> derivable_pt f x -> derivable_pt (/ f) x.
Proof.
  intros f x H X; cut (derivable_pt (fct_cte 1 / f) x -> derivable_pt (/ f) x).
  intro X0; apply X0.
  apply derivable_pt_div.
  apply derivable_pt_const.
  assumption.
  assumption.
  unfold div_fct, inv_fct, fct_cte; intros (x0,p);
    unfold derivable_pt; exists x0;
      unfold derivable_pt_abs; unfold derivable_pt_lim;
        unfold derivable_pt_abs in p; unfold derivable_pt_lim in p;
          intros; elim (p eps H0); intros; exists x1; intros;
            unfold Rdiv in H1; unfold Rdiv; rewrite <- (Rmult_1_l (/ f x));
              rewrite <- (Rmult_1_l (/ f (x + h))).
  apply H1; assumption.
Qed.

(**********)
Lemma pr_nu_var :
  forall (f g:R -> R) (x:R) (pr1:derivable_pt f x) (pr2:derivable_pt g x),
    f = g -> derive_pt f x pr1 = derive_pt g x pr2.
Proof.
  unfold derivable_pt, derive_pt; intros f g x (x0,p0) (x1,p1) ->.
  apply uniqueness_limite with g x; assumption.
Qed.

(**********)
Lemma pr_nu_var2 :
  forall (f g:R -> R) (x:R) (pr1:derivable_pt f x) (pr2:derivable_pt g x),
    (forall h:R, f h = g h) -> derive_pt f x pr1 = derive_pt g x pr2.
Proof.
  unfold derivable_pt, derive_pt; intros f g x (x0,p0) (x1,p1) H.
  assert (H0 := uniqueness_step2 _ _ _ p0).
  assert (H1 := uniqueness_step2 _ _ _ p1).
  cut (limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> 0) x1 0).
  intro H2; assert (H3 := uniqueness_step1 _ _ _ _ H0 H2).
  assumption.
  unfold limit1_in; unfold limit_in; unfold dist;
    simpl; unfold R_dist; unfold limit1_in in H1;
      unfold limit_in in H1; unfold dist in H1; simpl in H1;
        unfold R_dist in H1.
  intros; elim (H1 eps H2); intros.
  elim H3; intros.
  exists x2.
  split.
  assumption.
  intros; do 2 rewrite H; apply H5; assumption.
Qed.

(**********)
Lemma derivable_inv :
  forall f:R -> R, (forall x:R, f x <> 0) -> derivable f -> derivable (/ f).
Proof.
  intros f H X.
  unfold derivable; intro x.
  apply derivable_pt_inv.
  apply (H x).
  apply (X x).
Qed.

Lemma derive_pt_inv :
  forall (f:R -> R) (x:R) (pr:derivable_pt f x) (na:f x <> 0),
    derive_pt (/ f) x (derivable_pt_inv f x na pr) =
    - derive_pt f x pr / Rsqr (f x).
Proof.
  intros;
    replace (derive_pt (/ f) x (derivable_pt_inv f x na pr)) with
    (derive_pt (fct_cte 1 / f) x
      (derivable_pt_div (fct_cte 1) f x (derivable_pt_const 1 x) pr na)).
  rewrite derive_pt_div; rewrite derive_pt_const; unfold fct_cte;
    rewrite Rmult_0_l; rewrite Rmult_1_r; unfold Rminus;
      rewrite Rplus_0_l; reflexivity.
  apply pr_nu_var2.
  intro; unfold div_fct, fct_cte, inv_fct.
  unfold Rdiv; ring.
Qed.

(** Rabsolu *)
Lemma Rabs_derive_1 : forall x:R, 0 < x -> derivable_pt_lim Rabs x 1.
Proof.
  intros.
  unfold derivable_pt_lim; intros.
  exists (mkposreal x H); intros.
  rewrite (Rabs_right x).
  rewrite (Rabs_right (x + h)).
  rewrite Rplus_comm.
  unfold Rminus; rewrite Rplus_assoc; rewrite Rplus_opp_r.
  rewrite Rplus_0_r; unfold Rdiv; rewrite <- Rinv_r_sym.
  rewrite Rplus_opp_r; rewrite Rabs_R0; apply H0.
  apply H1.
  apply Rle_ge.
  destruct (Rcase_abs h) as [Hlt|Hgt].
  rewrite (Rabs_left h Hlt) in H2.
  left; rewrite Rplus_comm; apply Rplus_lt_reg_l with (- h); rewrite Rplus_0_r;
    rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
      apply H2.
  apply Rplus_le_le_0_compat.
  left; apply H.
  apply Rge_le; apply Hgt.
  left; apply H.
Qed.

Lemma Rabs_derive_2 : forall x:R, x < 0 -> derivable_pt_lim Rabs x (-1).
Proof.
  intros.
  unfold derivable_pt_lim; intros.
  cut (0 < - x).
  intro; exists (mkposreal (- x) H1); intros.
  rewrite (Rabs_left x).
  rewrite (Rabs_left (x + h)).
  replace ((-(x + h) - - x) / h - -1) with 0 by now field.
  rewrite Rabs_R0; apply H0.
  destruct (Rcase_abs h) as [Hlt|Hgt].
  apply Ropp_lt_cancel.
  rewrite Ropp_0; rewrite Ropp_plus_distr; apply Rplus_lt_0_compat.
  apply H1.
  apply Ropp_0_gt_lt_contravar; apply Hlt.
  rewrite (Rabs_right h Hgt) in H3.
  apply Rplus_lt_reg_l with (- x); rewrite Rplus_0_r; rewrite <- Rplus_assoc;
    rewrite Rplus_opp_l; rewrite Rplus_0_l; apply H3.
  apply H.
  apply Ropp_0_gt_lt_contravar; apply H.
Qed.

(** Rabsolu is derivable for all x <> 0 *)
Lemma Rderivable_pt_abs : forall x:R, x <> 0 -> derivable_pt Rabs x.
Proof.
  intros.
  destruct (total_order_T x 0) as [[Hlt|Heq]|Hgt].
  unfold derivable_pt; exists (-1).
  apply (Rabs_derive_2 x Hlt).
  elim H; exact Heq.
  unfold derivable_pt; exists 1.
  apply (Rabs_derive_1 x Hgt).
Qed.

(** Rabsolu is continuous for all x *)
Lemma Rcontinuity_abs : continuity Rabs.
Proof.
  unfold continuity; intro.
  case (Req_dec x 0); intro.
  unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      simpl; unfold R_dist; intros; exists eps;
        split.
  apply H0.
  intros; rewrite H; rewrite Rabs_R0; unfold Rminus; rewrite Ropp_0;
    rewrite Rplus_0_r; rewrite Rabs_Rabsolu; elim H1;
      intros; rewrite H in H3; unfold Rminus in H3; rewrite Ropp_0 in H3;
        rewrite Rplus_0_r in H3; apply H3.
  apply derivable_continuous_pt; apply (Rderivable_pt_abs x H).
Qed.

(** Finite sums : Sum a_k x^k *)
Lemma continuity_finite_sum :
  forall (An:nat -> R) (N:nat),
    continuity (fun y:R => sum_f_R0 (fun k:nat => An k * y ^ k) N).
Proof.
  intros; unfold continuity; intro.
  induction  N as [| N HrecN].
  simpl.
  apply continuity_pt_const.
  unfold constant; intros; reflexivity.
  replace (fun y:R => sum_f_R0 (fun k:nat => An k * y ^ k) (S N)) with
  ((fun y:R => sum_f_R0 (fun k:nat => (An k * y ^ k)%R) N) +
    (fun y:R => (An (S N) * y ^ S N)%R))%F.
  apply continuity_pt_plus.
  apply HrecN.
  replace (fun y:R => An (S N) * y ^ S N) with
  (mult_real_fct (An (S N)) (fun y:R => y ^ S N)).
  apply continuity_pt_scal.
  apply derivable_continuous_pt.
  apply derivable_pt_pow.
  reflexivity.
  reflexivity.
Qed.

Lemma derivable_pt_lim_fs :
  forall (An:nat -> R) (x:R) (N:nat),
    (0 < N)%nat ->
    derivable_pt_lim (fun y:R => sum_f_R0 (fun k:nat => An k * y ^ k) N) x
    (sum_f_R0 (fun k:nat => INR (S k) * An (S k) * x ^ k) (pred N)).
Proof.
  intros; induction  N as [| N HrecN].
  elim (lt_irrefl _ H).
  cut (N = 0%nat \/ (0 < N)%nat).
  intro; elim H0; intro.
  rewrite H1.
  simpl.
  replace (fun y:R => An 0%nat * 1 + An 1%nat * (y * 1)) with
  (fct_cte (An 0%nat * 1) + mult_real_fct (An 1%nat) (id * fct_cte 1))%F.
  replace (1 * An 1%nat * 1) with (0 + An 1%nat * (1 * fct_cte 1 x + id x * 0)).
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  unfold fct_cte, id; ring.
  reflexivity.
  replace (fun y:R => sum_f_R0 (fun k:nat => An k * y ^ k) (S N)) with
  ((fun y:R => sum_f_R0 (fun k:nat => (An k * y ^ k)%R) N) +
    (fun y:R => (An (S N) * y ^ S N)%R))%F.
  replace (sum_f_R0 (fun k:nat => INR (S k) * An (S k) * x ^ k) (pred (S N)))
    with
      (sum_f_R0 (fun k:nat => INR (S k) * An (S k) * x ^ k) (pred N) +
        An (S N) * (INR (S (pred (S N))) * x ^ pred (S N))).
  apply derivable_pt_lim_plus.
  apply HrecN.
  assumption.
  replace (fun y:R => An (S N) * y ^ S N) with
  (mult_real_fct (An (S N)) (fun y:R => y ^ S N)).
  apply derivable_pt_lim_scal.
  replace (pred (S N)) with N; [ idtac | reflexivity ].
  pattern N at 3; replace N with (pred (S N)).
  apply derivable_pt_lim_pow.
  reflexivity.
  reflexivity.
  cut (pred (S N) = S (pred N)).
  intro; rewrite H2.
  rewrite tech5.
  apply Rplus_eq_compat_l.
  rewrite <- H2.
  replace (pred (S N)) with N; [ idtac | reflexivity ].
  ring.
  simpl.
  apply S_pred with 0%nat; assumption.
  unfold plus_fct.
  simpl; reflexivity.
  inversion H.
  left; reflexivity.
  right; apply lt_le_trans with 1%nat; [ apply lt_O_Sn | assumption ].
Qed.

Lemma derivable_pt_lim_finite_sum :
  forall (An:nat -> R) (x:R) (N:nat),
    derivable_pt_lim (fun y:R => sum_f_R0 (fun k:nat => An k * y ^ k) N) x
    match N with
      | O => 0
      | _ => sum_f_R0 (fun k:nat => INR (S k) * An (S k) * x ^ k) (pred N)
    end.
Proof.
  intros.
  induction  N as [| N HrecN].
  simpl.
  rewrite Rmult_1_r.
  replace (fun _:R => An 0%nat) with (fct_cte (An 0%nat));
  [ apply derivable_pt_lim_const | reflexivity ].
  apply derivable_pt_lim_fs; apply lt_O_Sn.
Qed.

Lemma derivable_pt_finite_sum :
  forall (An:nat -> R) (N:nat) (x:R),
    derivable_pt (fun y:R => sum_f_R0 (fun k:nat => An k * y ^ k) N) x.
Proof.
  intros.
  unfold derivable_pt.
  assert (H := derivable_pt_lim_finite_sum An x N).
  induction  N as [| N HrecN].
  exists 0; apply H.
  exists
    (sum_f_R0 (fun k:nat => INR (S k) * An (S k) * x ^ k) (pred (S N)));
    apply H.
Qed.

Lemma derivable_finite_sum :
  forall (An:nat -> R) (N:nat),
    derivable (fun y:R => sum_f_R0 (fun k:nat => An k * y ^ k) N).
Proof.
  intros; unfold derivable; intro; apply derivable_pt_finite_sum.
Qed.

(** Regularity of hyperbolic functions *)
Lemma derivable_pt_lim_cosh : forall x:R, derivable_pt_lim cosh x (sinh x).
Proof.
  intro.
  unfold cosh, sinh; unfold Rdiv.
  replace (fun x0:R => (exp x0 + exp (- x0)) * / 2) with
  ((exp + comp exp (- id)) * fct_cte (/ 2))%F; [ idtac | reflexivity ].
  replace ((exp x - exp (- x)) * / 2) with
  ((exp x + exp (- x) * -1) * fct_cte (/ 2) x +
    (exp + comp exp (- id))%F x * 0).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_exp.
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_opp.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_exp.
  apply derivable_pt_lim_const.
  unfold plus_fct, mult_real_fct, comp, opp_fct, id, fct_cte; ring.
Qed.

Lemma derivable_pt_lim_sinh : forall x:R, derivable_pt_lim sinh x (cosh x).
Proof.
  intro.
  unfold cosh, sinh; unfold Rdiv.
  replace (fun x0:R => (exp x0 - exp (- x0)) * / 2) with
  ((exp - comp exp (- id)) * fct_cte (/ 2))%F; [ idtac | reflexivity ].
  replace ((exp x + exp (- x)) * / 2) with
  ((exp x - exp (- x) * -1) * fct_cte (/ 2) x +
    (exp - comp exp (- id))%F x * 0).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_exp.
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_opp.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_exp.
  apply derivable_pt_lim_const.
  unfold plus_fct, mult_real_fct, comp, opp_fct, id, fct_cte; ring.
Qed.

Lemma derivable_pt_exp : forall x:R, derivable_pt exp x.
Proof.
  intro.
  unfold derivable_pt.
  exists (exp x).
  apply derivable_pt_lim_exp.
Qed.

Lemma derivable_pt_cosh : forall x:R, derivable_pt cosh x.
Proof.
  intro.
  unfold derivable_pt.
  exists (sinh x).
  apply derivable_pt_lim_cosh.
Qed.

Lemma derivable_pt_sinh : forall x:R, derivable_pt sinh x.
Proof.
  intro.
  unfold derivable_pt.
  exists (cosh x).
  apply derivable_pt_lim_sinh.
Qed.

Lemma derivable_exp : derivable exp.
Proof.
  unfold derivable; apply derivable_pt_exp.
Qed.

Lemma derivable_cosh : derivable cosh.
Proof.
  unfold derivable; apply derivable_pt_cosh.
Qed.

Lemma derivable_sinh : derivable sinh.
Proof.
  unfold derivable; apply derivable_pt_sinh.
Qed.

Lemma derive_pt_exp :
  forall x:R, derive_pt exp x (derivable_pt_exp x) = exp x.
Proof.
  intro; apply derive_pt_eq_0.
  apply derivable_pt_lim_exp.
Qed.

Lemma derive_pt_cosh :
  forall x:R, derive_pt cosh x (derivable_pt_cosh x) = sinh x.
Proof.
  intro; apply derive_pt_eq_0.
  apply derivable_pt_lim_cosh.
Qed.

Lemma derive_pt_sinh :
  forall x:R, derive_pt sinh x (derivable_pt_sinh x) = cosh x.
Proof.
  intro; apply derive_pt_eq_0.
  apply derivable_pt_lim_sinh.
Qed.

Lemma sinh_lt : forall x y, x < y -> sinh x < sinh y.
intros x y xy; destruct (MVT_cor2 sinh cosh x y xy) as [c [Pc _]].
 intros; apply derivable_pt_lim_sinh.
apply Rplus_lt_reg_l with (Ropp (sinh x)); rewrite Rplus_opp_l, Rplus_comm.
unfold Rminus at 1 in Pc; rewrite Pc; apply Rmult_lt_0_compat;[ | ].
 unfold cosh; apply Rmult_lt_0_compat;[|apply Rinv_0_lt_compat, Rlt_0_2].
 now apply Rplus_lt_0_compat; apply exp_pos.
now apply Rlt_Rminus; assumption.
Qed.

