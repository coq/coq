(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Ranalysis1.
Require Import Max.
Require Import Even.
Open Local Scope R_scope.

Definition Boule (x:R) (r:posreal) (y:R) : Prop := Rabs (y - x) < r.

(** Uniform convergence *)
Definition CVU (fn:nat -> R -> R) (f:R -> R) (x:R)
  (r:posreal) : Prop :=
  forall eps:R,
    0 < eps ->
    exists N : nat,
      (forall (n:nat) (y:R),
        (N <= n)%nat -> Boule x r y -> Rabs (f y - fn n y) < eps).

(** Normal convergence *)
Definition CVN_r (fn:nat -> R -> R) (r:posreal) : Type :=
  { An:nat -> R &
    { l:R |
      Un_cv (fun n:nat => sum_f_R0 (fun k:nat => Rabs (An k)) n) l /\
      (forall (n:nat) (y:R), Boule 0 r y -> Rabs (fn n y) <= An n) } }.

Definition CVN_R (fn:nat -> R -> R) : Type := forall r:posreal, CVN_r fn r.

Definition SFL (fn:nat -> R -> R)
  (cv:forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l })
  (y:R) : R := let (a,_) := cv y in a.

(** In a complete space, normal convergence implies uniform convergence *)
Lemma CVN_CVU :
  forall (fn:nat -> R -> R)
    (cv:forall x:R, {l:R | Un_cv (fun N:nat => SP fn N x) l })
    (r:posreal), CVN_r fn r -> CVU (fun n:nat => SP fn n) (SFL fn cv) 0 r.
Proof.
  intros; unfold CVU in |- *; intros.
  unfold CVN_r in X.
  elim X; intros An X0.
  elim X0; intros s H0.
  elim H0; intros.
  cut (Un_cv (fun n:nat => sum_f_R0 (fun k:nat => Rabs (An k)) n - s) 0).
  intro; unfold Un_cv in H3.
  elim (H3 eps H); intros N0 H4.
  exists N0; intros.
  apply Rle_lt_trans with (Rabs (sum_f_R0 (fun k:nat => Rabs (An k)) n - s)).
  rewrite <- (Rabs_Ropp (sum_f_R0 (fun k:nat => Rabs (An k)) n - s));
    rewrite Ropp_minus_distr';
      rewrite (Rabs_right (s - sum_f_R0 (fun k:nat => Rabs (An k)) n)).
  eapply sum_maj1.
  unfold SFL in |- *; case (cv y); intro.
  trivial.
  apply H1.
  intro; elim H0; intros.
  rewrite (Rabs_right (An n0)).
  apply H8; apply H6.
  apply Rle_ge; apply Rle_trans with (Rabs (fn n0 y)).
  apply Rabs_pos.
  apply H8; apply H6.
  apply Rle_ge;
    apply Rplus_le_reg_l with (sum_f_R0 (fun k:nat => Rabs (An k)) n).
  rewrite Rplus_0_r; unfold Rminus in |- *; rewrite (Rplus_comm s);
    rewrite <- Rplus_assoc; rewrite Rplus_opp_r; rewrite Rplus_0_l;
      apply sum_incr.
  apply H1.
  intro; apply Rabs_pos.
  unfold R_dist in H4; unfold Rminus in H4; rewrite Ropp_0 in H4.
  assert (H7 := H4 n H5).
  rewrite Rplus_0_r in H7; apply H7.
  unfold Un_cv in H1; unfold Un_cv in |- *; intros.
  elim (H1 _ H3); intros.
  exists x; intros.
  unfold R_dist in |- *; unfold R_dist in H4.
  rewrite Rminus_0_r; apply H4; assumption.
Qed.

(** Each limit of a sequence of functions which converges uniformly is continue *)
Lemma CVU_continuity :
  forall (fn:nat -> R -> R) (f:R -> R) (x:R) (r:posreal),
    CVU fn f x r ->
    (forall (n:nat) (y:R), Boule x r y -> continuity_pt (fn n) y) ->
    forall y:R, Boule x r y -> continuity_pt f y.
Proof.
  intros; unfold continuity_pt in |- *; unfold continue_in in |- *;
    unfold limit1_in in |- *; unfold limit_in in |- *;
      simpl in |- *; unfold R_dist in |- *; intros.
  unfold CVU in H.
  cut (0 < eps / 3);
    [ intro
      | unfold Rdiv in |- *; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H _ H3); intros N0 H4.
  assert (H5 := H0 N0 y H1).
  cut (exists del : posreal, (forall h:R, Rabs h < del -> Boule x r (y + h))).
  intro.
  elim H6; intros del1 H7.
  unfold continuity_pt in H5; unfold continue_in in H5; unfold limit1_in in H5;
    unfold limit_in in H5; simpl in H5; unfold R_dist in H5.
  elim (H5 _ H3); intros del2 H8.
  set (del := Rmin del1 del2).
  exists del; intros.
  split.
  unfold del in |- *; unfold Rmin in |- *; case (Rle_dec del1 del2); intro.
  apply (cond_pos del1).
  elim H8; intros; assumption.
  intros;
    apply Rle_lt_trans with (Rabs (f x0 - fn N0 x0) + Rabs (fn N0 x0 - f y)).
  replace (f x0 - f y) with (f x0 - fn N0 x0 + (fn N0 x0 - f y));
  [ apply Rabs_triang | ring ].
  apply Rle_lt_trans with
    (Rabs (f x0 - fn N0 x0) + Rabs (fn N0 x0 - fn N0 y) + Rabs (fn N0 y - f y)).
  rewrite Rplus_assoc; apply Rplus_le_compat_l.
  replace (fn N0 x0 - f y) with (fn N0 x0 - fn N0 y + (fn N0 y - f y));
  [ apply Rabs_triang | ring ].
  replace eps with (eps / 3 + eps / 3 + eps / 3).
  repeat apply Rplus_lt_compat.
  apply H4.
  apply le_n.
  replace x0 with (y + (x0 - y)); [ idtac | ring ]; apply H7.
  elim H9; intros.
  apply Rlt_le_trans with del.
  assumption.
  unfold del in |- *; apply Rmin_l.
  elim H8; intros.
  apply H11.
  split.
  elim H9; intros; assumption.
  elim H9; intros; apply Rlt_le_trans with del.
  assumption.
  unfold del in |- *; apply Rmin_r.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr'; apply H4.
  apply le_n.
  assumption.
  apply Rmult_eq_reg_l with 3.
  do 2 rewrite Rmult_plus_distr_l; unfold Rdiv in |- *; rewrite <- Rmult_assoc;
    rewrite Rinv_r_simpl_m.
  ring.
  discrR.
  discrR.
  cut (0 < r - Rabs (x - y)).
  intro; exists (mkposreal _ H6).
  simpl in |- *; intros.
  unfold Boule in |- *; replace (y + h - x) with (h + (y - x));
    [ idtac | ring ]; apply Rle_lt_trans with (Rabs h + Rabs (y - x)).
  apply Rabs_triang.
  apply Rplus_lt_reg_r with (- Rabs (x - y)).
  rewrite <- (Rabs_Ropp (y - x)); rewrite Ropp_minus_distr'.
  replace (- Rabs (x - y) + r) with (r - Rabs (x - y)).
  replace (- Rabs (x - y) + (Rabs h + Rabs (x - y))) with (Rabs h).
  apply H7.
  ring.
  ring.
  unfold Boule in H1; rewrite <- (Rabs_Ropp (x - y)); rewrite Ropp_minus_distr';
    apply Rplus_lt_reg_r with (Rabs (y - x)).
  rewrite Rplus_0_r; replace (Rabs (y - x) + (r - Rabs (y - x))) with (pos r);
    [ apply H1 | ring ].
Qed.

(**********)
Lemma continuity_pt_finite_SF :
  forall (fn:nat -> R -> R) (N:nat) (x:R),
    (forall n:nat, (n <= N)%nat -> continuity_pt (fn n) x) ->
    continuity_pt (fun y:R => sum_f_R0 (fun k:nat => fn k y) N) x.
Proof.
  intros; induction  N as [| N HrecN].
  simpl in |- *; apply (H 0%nat); apply le_n.
  simpl in |- *;
    replace (fun y:R => sum_f_R0 (fun k:nat => fn k y) N + fn (S N) y) with
    ((fun y:R => sum_f_R0 (fun k:nat => fn k y) N) + (fun y:R => fn (S N) y))%F;
    [ idtac | reflexivity ].
  apply continuity_pt_plus.
  apply HrecN.
  intros; apply H.
  apply le_trans with N; [ assumption | apply le_n_Sn ].
  apply (H (S N)); apply le_n.
Qed.

(** Continuity and normal convergence *)
Lemma SFL_continuity_pt :
  forall (fn:nat -> R -> R)
    (cv:forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l })
    (r:posreal),
    CVN_r fn r ->
    (forall (n:nat) (y:R), Boule 0 r y -> continuity_pt (fn n) y) ->
    forall y:R, Boule 0 r y -> continuity_pt (SFL fn cv) y.
Proof.
  intros; eapply CVU_continuity.
  apply CVN_CVU.
  apply X.
  intros; unfold SP in |- *; apply continuity_pt_finite_SF.
  intros; apply H.
  apply H1.
  apply H0.
Qed.

Lemma SFL_continuity :
  forall (fn:nat -> R -> R)
    (cv:forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l }),
    CVN_R fn -> (forall n:nat, continuity (fn n)) -> continuity (SFL fn cv).
Proof.
  intros; unfold continuity in |- *; intro.
  cut (0 < Rabs x + 1);
    [ intro | apply Rplus_le_lt_0_compat; [ apply Rabs_pos | apply Rlt_0_1 ] ].
  cut (Boule 0 (mkposreal _ H0) x).
  intro; eapply SFL_continuity_pt with (mkposreal _ H0).
  apply X.
  intros; apply (H n y).
  apply H1.
  unfold Boule in |- *; simpl in |- *; rewrite Rminus_0_r;
    pattern (Rabs x) at 1 in |- *; rewrite <- Rplus_0_r;
      apply Rplus_lt_compat_l; apply Rlt_0_1.
Qed.

(** As R is complete, normal convergence implies that (fn) is simply-uniformly convergent *)
Lemma CVN_R_CVS :
  forall fn:nat -> R -> R,
    CVN_R fn -> forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l }.
Proof.
  intros; apply R_complete.
  unfold SP in |- *; set (An := fun N:nat => fn N x).
  change (Cauchy_crit_series An) in |- *.
  apply cauchy_abs.
  unfold Cauchy_crit_series in |- *; apply CV_Cauchy.
  unfold CVN_R in X; cut (0 < Rabs x + 1).
  intro; assert (H0 := X (mkposreal _ H)).
  unfold CVN_r in H0; elim H0; intros Bn H1.
  elim H1; intros l H2.
  elim H2; intros.
  apply Rseries_CV_comp with Bn.
  intro; split.
  apply Rabs_pos.
  unfold An in |- *; apply H4; unfold Boule in |- *; simpl in |- *;
    rewrite Rminus_0_r.
  pattern (Rabs x) at 1 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l;
    apply Rlt_0_1.
  exists l.
  cut (forall n:nat, 0 <= Bn n).
  intro; unfold Un_cv in H3; unfold Un_cv in |- *; intros.
  elim (H3 _ H6); intros.
  exists x0; intros.
  replace (sum_f_R0 Bn n) with (sum_f_R0 (fun k:nat => Rabs (Bn k)) n).
  apply H7; assumption.
  apply sum_eq; intros; apply Rabs_right; apply Rle_ge; apply H5.
  intro; apply Rle_trans with (Rabs (An n)).
  apply Rabs_pos.
  unfold An in |- *; apply H4; unfold Boule in |- *; simpl in |- *;
    rewrite Rminus_0_r; pattern (Rabs x) at 1 in |- *;
      rewrite <- Rplus_0_r; apply Rplus_lt_compat_l; apply Rlt_0_1.
  apply Rplus_le_lt_0_compat; [ apply Rabs_pos | apply Rlt_0_1 ].
Qed.
