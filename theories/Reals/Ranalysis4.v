(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis1.
Require Import Ranalysis3.
Require Import Exp_prop.
Open Local Scope R_scope.

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
  unfold div_fct, inv_fct, fct_cte in |- *; intro X0; elim X0; intros;
    unfold derivable_pt in |- *; exists x0;
      unfold derivable_pt_abs in |- *; unfold derivable_pt_lim in |- *;
        unfold derivable_pt_abs in p; unfold derivable_pt_lim in p; 
          intros; elim (p eps H0); intros; exists x1; intros; 
            unfold Rdiv in H1; unfold Rdiv in |- *; rewrite <- (Rmult_1_l (/ f x));
              rewrite <- (Rmult_1_l (/ f (x + h))).
  apply H1; assumption.
Qed.

(**********)
Lemma pr_nu_var :
  forall (f g:R -> R) (x:R) (pr1:derivable_pt f x) (pr2:derivable_pt g x),
    f = g -> derive_pt f x pr1 = derive_pt g x pr2.
Proof.
  unfold derivable_pt, derive_pt in |- *; intros.
  elim pr1; intros.
  elim pr2; intros.
  simpl in |- *.
  rewrite H in p.
  apply uniqueness_limite with g x; assumption.
Qed.

(**********)
Lemma pr_nu_var2 :
  forall (f g:R -> R) (x:R) (pr1:derivable_pt f x) (pr2:derivable_pt g x),
    (forall h:R, f h = g h) -> derive_pt f x pr1 = derive_pt g x pr2.
Proof.
  unfold derivable_pt, derive_pt in |- *; intros.
  elim pr1; intros.
  elim pr2; intros.
  simpl in |- *.
  assert (H0 := uniqueness_step2 _ _ _ p). 
  assert (H1 := uniqueness_step2 _ _ _ p0). 
  cut (limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> 0) x1 0).
  intro; assert (H3 := uniqueness_step1 _ _ _ _ H0 H2). 
  assumption.
  unfold limit1_in in |- *; unfold limit_in in |- *; unfold dist in |- *;
    simpl in |- *; unfold R_dist in |- *; unfold limit1_in in H1;
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
  unfold derivable in |- *; intro x.
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
  rewrite derive_pt_div; rewrite derive_pt_const; unfold fct_cte in |- *;
    rewrite Rmult_0_l; rewrite Rmult_1_r; unfold Rminus in |- *;
      rewrite Rplus_0_l; reflexivity.
  apply pr_nu_var2.
  intro; unfold div_fct, fct_cte, inv_fct in |- *.
  unfold Rdiv in |- *; ring.
Qed.

(** Rabsolu *)
Lemma Rabs_derive_1 : forall x:R, 0 < x -> derivable_pt_lim Rabs x 1.
Proof.
  intros.
  unfold derivable_pt_lim in |- *; intros.
  exists (mkposreal x H); intros.
  rewrite (Rabs_right x).
  rewrite (Rabs_right (x + h)).
  rewrite Rplus_comm.
  unfold Rminus in |- *; rewrite Rplus_assoc; rewrite Rplus_opp_r.
  rewrite Rplus_0_r; unfold Rdiv in |- *; rewrite <- Rinv_r_sym.
  rewrite Rplus_opp_r; rewrite Rabs_R0; apply H0.
  apply H1.
  apply Rle_ge.
  case (Rcase_abs h); intro.
  rewrite (Rabs_left h r) in H2.
  left; rewrite Rplus_comm; apply Rplus_lt_reg_r with (- h); rewrite Rplus_0_r;
    rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l; 
      apply H2.
  apply Rplus_le_le_0_compat.
  left; apply H.
  apply Rge_le; apply r.
  left; apply H.
Qed.

Lemma Rabs_derive_2 : forall x:R, x < 0 -> derivable_pt_lim Rabs x (-1).
Proof.
  intros.
  unfold derivable_pt_lim in |- *; intros.
  cut (0 < - x).
  intro; exists (mkposreal (- x) H1); intros.
  rewrite (Rabs_left x).
  rewrite (Rabs_left (x + h)).
  rewrite Rplus_comm.
  rewrite Ropp_plus_distr.
  unfold Rminus in |- *; rewrite Ropp_involutive; rewrite Rplus_assoc;
    rewrite Rplus_opp_l.
  rewrite Rplus_0_r; unfold Rdiv in |- *.
  rewrite Ropp_mult_distr_l_reverse.
  rewrite <- Rinv_r_sym.
  rewrite Ropp_involutive; rewrite Rplus_opp_l; rewrite Rabs_R0; apply H0.
  apply H2.
  case (Rcase_abs h); intro.
  apply Ropp_lt_cancel.
  rewrite Ropp_0; rewrite Ropp_plus_distr; apply Rplus_lt_0_compat.
  apply H1.
  apply Ropp_0_gt_lt_contravar; apply r.
  rewrite (Rabs_right h r) in H3.
  apply Rplus_lt_reg_r with (- x); rewrite Rplus_0_r; rewrite <- Rplus_assoc;
    rewrite Rplus_opp_l; rewrite Rplus_0_l; apply H3.
  apply H.
  apply Ropp_0_gt_lt_contravar; apply H.
Qed.

(** Rabsolu is derivable for all x <> 0 *)
Lemma Rderivable_pt_abs : forall x:R, x <> 0 -> derivable_pt Rabs x.
Proof.
  intros.
  case (total_order_T x 0); intro.
  elim s; intro.
  unfold derivable_pt in |- *; exists (-1).
  apply (Rabs_derive_2 x a).
  elim H; exact b.
  unfold derivable_pt in |- *; exists 1.
  apply (Rabs_derive_1 x r).
Qed.

(** Rabsolu is continuous for all x *)
Lemma Rcontinuity_abs : continuity Rabs.
Proof.
  unfold continuity in |- *; intro.
  case (Req_dec x 0); intro.
  unfold continuity_pt in |- *; unfold continue_in in |- *;
    unfold limit1_in in |- *; unfold limit_in in |- *; 
      simpl in |- *; unfold R_dist in |- *; intros; exists eps; 
        split.
  apply H0.
  intros; rewrite H; rewrite Rabs_R0; unfold Rminus in |- *; rewrite Ropp_0;
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
  intros; unfold continuity in |- *; intro.
  induction  N as [| N HrecN].
  simpl in |- *.
  apply continuity_pt_const.
  unfold constant in |- *; intros; reflexivity.
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
  simpl in |- *.
  replace (fun y:R => An 0%nat * 1 + An 1%nat * (y * 1)) with
  (fct_cte (An 0%nat * 1) + mult_real_fct (An 1%nat) (id * fct_cte 1))%F.
  replace (1 * An 1%nat * 1) with (0 + An 1%nat * (1 * fct_cte 1 x + id x * 0)).
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  unfold fct_cte, id in |- *; ring.
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
  pattern N at 3 in |- *; replace N with (pred (S N)).
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
  simpl in |- *.
  apply S_pred with 0%nat; assumption.
  unfold plus_fct in |- *.
  simpl in |- *; reflexivity.
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
  simpl in |- *.
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
  unfold derivable_pt in |- *.
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
  intros; unfold derivable in |- *; intro; apply derivable_pt_finite_sum.
Qed.

(** Regularity of hyperbolic functions *)
Lemma derivable_pt_lim_cosh : forall x:R, derivable_pt_lim cosh x (sinh x).
Proof.
  intro.
  unfold cosh, sinh in |- *; unfold Rdiv in |- *.
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
  unfold plus_fct, mult_real_fct, comp, opp_fct, id, fct_cte in |- *; ring.
Qed.

Lemma derivable_pt_lim_sinh : forall x:R, derivable_pt_lim sinh x (cosh x).
Proof.
  intro.
  unfold cosh, sinh in |- *; unfold Rdiv in |- *.
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
  unfold plus_fct, mult_real_fct, comp, opp_fct, id, fct_cte in |- *; ring.
Qed.

Lemma derivable_pt_exp : forall x:R, derivable_pt exp x.
Proof.
  intro.
  unfold derivable_pt in |- *.
  exists (exp x).
  apply derivable_pt_lim_exp.
Qed.

Lemma derivable_pt_cosh : forall x:R, derivable_pt cosh x.
Proof.
  intro.
  unfold derivable_pt in |- *.
  exists (sinh x).
  apply derivable_pt_lim_cosh.
Qed.

Lemma derivable_pt_sinh : forall x:R, derivable_pt sinh x.
Proof.
  intro.
  unfold derivable_pt in |- *.
  exists (cosh x).
  apply derivable_pt_lim_sinh.
Qed.

Lemma derivable_exp : derivable exp.
Proof.
  unfold derivable in |- *; apply derivable_pt_exp.
Qed.

Lemma derivable_cosh : derivable cosh.
Proof.
  unfold derivable in |- *; apply derivable_pt_cosh.
Qed.

Lemma derivable_sinh : derivable sinh.
Proof.
  unfold derivable in |- *; apply derivable_pt_sinh.
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
