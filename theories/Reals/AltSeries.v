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
Require Import Rseries.
Require Import SeqProp.
Require Import PartSum.
Require Import Max.
Local Open Scope R_scope.

(**********)
(** * Formalization of alternated series *)
Definition tg_alt (Un:nat -> R) (i:nat) : R := (-1) ^ i * Un i.
Definition positivity_seq (Un:nat -> R) : Prop := forall n:nat, 0 <= Un n.

Lemma CV_ALT_step0 :
  forall Un:nat -> R,
    Un_decreasing Un ->
    Un_growing (fun N:nat => sum_f_R0 (tg_alt Un) (S (2 * N))).
Proof.
  intros; unfold Un_growing; intro.
  cut ((2 * S n)%nat = S (S (2 * n))).
  intro; rewrite H0.
  do 4 rewrite tech5; repeat rewrite Rplus_assoc; apply Rplus_le_compat_l.
  pattern (tg_alt Un (S (2 * n))) at 1; rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  unfold tg_alt; rewrite <- H0; rewrite pow_1_odd; rewrite pow_1_even;
    rewrite Rmult_1_l.
  apply Rplus_le_reg_l with (Un (S (2 * S n))).
  rewrite Rplus_0_r;
    replace (Un (S (2 * S n)) + (Un (2 * S n)%nat + -1 * Un (S (2 * S n)))) with
      (Un (2 * S n)%nat); [ idtac | ring ].
  apply H.
  cut (forall n:nat, S n = (n + 1)%nat); [ intro | intro; ring ].
  rewrite (H0 n); rewrite (H0 (S (2 * n))); rewrite (H0 (2 * n)%nat); ring.
Qed.

Lemma CV_ALT_step1 :
  forall Un:nat -> R,
    Un_decreasing Un ->
    Un_decreasing (fun N:nat => sum_f_R0 (tg_alt Un) (2 * N)).
Proof.
  intros; unfold Un_decreasing; intro.
  cut ((2 * S n)%nat = S (S (2 * n))).
  intro; rewrite H0; do 2 rewrite tech5; repeat rewrite Rplus_assoc.
  pattern (sum_f_R0 (tg_alt Un) (2 * n)) at 2; rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  unfold tg_alt; rewrite <- H0; rewrite pow_1_odd; rewrite pow_1_even;
    rewrite Rmult_1_l.
  apply Rplus_le_reg_l with (Un (S (2 * n))).
  rewrite Rplus_0_r;
    replace (Un (S (2 * n)) + (-1 * Un (S (2 * n)) + Un (2 * S n)%nat)) with
      (Un (2 * S n)%nat); [ idtac | ring ].
  rewrite H0; apply H.
  cut (forall n:nat, S n = (n + 1)%nat); [ intro | intro; ring ].
  rewrite (H0 n); rewrite (H0 (S (2 * n))); rewrite (H0 (2 * n)%nat); ring.
Qed.

(**********)
Lemma CV_ALT_step2 :
  forall (Un:nat -> R) (N:nat),
    Un_decreasing Un ->
    positivity_seq Un ->
    sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * N)) <= 0.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; unfold tg_alt; simpl; rewrite Rmult_1_r.
  replace (-1 * -1 * Un 2%nat) with (Un 2%nat); [ idtac | ring ].
  apply Rplus_le_reg_l with (Un 1%nat); rewrite Rplus_0_r.
  replace (Un 1%nat + (-1 * Un 1%nat + Un 2%nat)) with (Un 2%nat);
    [ apply H | ring ].
  cut (S (2 * S N) = S (S (S (2 * N)))).
  intro; rewrite H1; do 2 rewrite tech5.
  apply Rle_trans with (sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * N))).
  pattern (sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * N))) at 2;
    rewrite <- Rplus_0_r.
  rewrite Rplus_assoc; apply Rplus_le_compat_l.
  unfold tg_alt; rewrite <- H1.
  rewrite pow_1_odd.
  cut (S (S (2 * S N)) = (2 * S (S N))%nat).
  intro; rewrite H2; rewrite pow_1_even; rewrite Rmult_1_l; rewrite <- H2.
  apply Rplus_le_reg_l with (Un (S (2 * S N))).
  rewrite Rplus_0_r;
    replace (Un (S (2 * S N)) + (-1 * Un (S (2 * S N)) + Un (S (S (2 * S N)))))
      with (Un (S (S (2 * S N)))); [ idtac | ring ].
  apply H.
  ring.
  apply HrecN.
  ring.
Qed.

(** A more general inequality *)
Lemma CV_ALT_step3 :
  forall (Un:nat -> R) (N:nat),
    Un_decreasing Un ->
    positivity_seq Un -> sum_f_R0 (fun i:nat => tg_alt Un (S i)) N <= 0.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; unfold tg_alt; simpl; rewrite Rmult_1_r.
  apply Rplus_le_reg_l with (Un 1%nat).
  rewrite Rplus_0_r; replace (Un 1%nat + -1 * Un 1%nat) with 0;
    [ apply H0 | ring ].
  assert (H1 := even_odd_cor N).
  elim H1; intros.
  elim H2; intro.
  rewrite H3; apply CV_ALT_step2; assumption.
  rewrite H3; rewrite tech5.
  apply Rle_trans with (sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * x))).
  pattern (sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * x))) at 2;
    rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  unfold tg_alt; simpl.
  replace (x + (x + 0))%nat with (2 * x)%nat; [ idtac | ring ].
  rewrite pow_1_even.
  replace (-1 * (-1 * (-1 * 1)) * Un (S (S (S (2 * x))))) with
    (- Un (S (S (S (2 * x))))); [ idtac | ring ].
  apply Rplus_le_reg_l with (Un (S (S (S (2 * x))))).
  rewrite Rplus_0_r; rewrite Rplus_opp_r.
  apply H0.
  apply CV_ALT_step2; assumption.
Qed.

  (**********)
Lemma CV_ALT_step4 :
  forall Un:nat -> R,
    Un_decreasing Un ->
    positivity_seq Un ->
    has_ub (fun N:nat => sum_f_R0 (tg_alt Un) (S (2 * N))).
Proof.
  intros; unfold has_ub; unfold bound.
  exists (Un 0%nat).
  unfold is_upper_bound; intros; elim H1; intros.
  rewrite H2; rewrite decomp_sum.
  replace (tg_alt Un 0) with (Un 0%nat).
  pattern (Un 0%nat) at 2; rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  apply CV_ALT_step3; assumption.
  unfold tg_alt; simpl; ring.
  apply lt_O_Sn.
Qed.

(** This lemma gives an interesting result about alternated series *)
Lemma CV_ALT :
  forall Un:nat -> R,
    Un_decreasing Un ->
    positivity_seq Un ->
    Un_cv Un 0 ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) N) l }.
Proof.
  intros.
  assert (H2 := CV_ALT_step0 _ H).
  assert (H3 := CV_ALT_step4 _ H H0).
  destruct (growing_cv _ H2 H3) as (x,p).
  exists x.
  unfold Un_cv; unfold R_dist; unfold Un_cv in H1;
    unfold R_dist in H1; unfold Un_cv in p; unfold R_dist in p.
  intros; cut (0 < eps / 2);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
	[ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H1 (eps / 2) H5); intros N2 H6.
  elim (p (eps / 2) H5); intros N1 H7.
  set (N := max (S (2 * N1)) N2).
  exists N; intros.
  assert (H9 := even_odd_cor n).
  elim H9; intros P H10.
  cut (N1 <= P)%nat.
  intro; elim H10; intro.
  replace (sum_f_R0 (tg_alt Un) n - x) with
    (sum_f_R0 (tg_alt Un) (S n) - x + - tg_alt Un (S n)).
  apply Rle_lt_trans with
    (Rabs (sum_f_R0 (tg_alt Un) (S n) - x) + Rabs (- tg_alt Un (S n))).
  apply Rabs_triang.
  rewrite (double_var eps); apply Rplus_lt_compat.
  rewrite H12; apply H7; assumption.
  rewrite Rabs_Ropp; unfold tg_alt; rewrite Rabs_mult;
    rewrite pow_1_abs; rewrite Rmult_1_l; unfold Rminus in H6;
      rewrite Ropp_0 in H6; rewrite <- (Rplus_0_r (Un (S n)));
	apply H6.
  unfold ge; apply le_trans with n.
  apply le_trans with N; [ unfold N; apply le_max_r | assumption ].
  apply le_n_Sn.
  rewrite tech5; ring.
  rewrite H12; apply Rlt_trans with (eps / 2).
  apply H7; assumption.
  unfold Rdiv; apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite (Rmult_comm 2); rewrite Rmult_assoc; rewrite <- Rinv_l_sym;
    [ rewrite Rmult_1_r | discrR ].
  rewrite double.
  pattern eps at 1; rewrite <- (Rplus_0_r eps); apply Rplus_lt_compat_l;
    assumption.
  elim H10; intro; apply le_double.
  rewrite <- H11; apply le_trans with N.
  unfold N; apply le_trans with (S (2 * N1));
    [ apply le_n_Sn | apply le_max_l ].
  assumption.
  apply lt_n_Sm_le.
  rewrite <- H11.
  apply lt_le_trans with N.
  unfold N; apply lt_le_trans with (S (2 * N1)).
  apply lt_n_Sn.
  apply le_max_l.
  assumption.
Qed.


(*************************************************)
(** *       Convergence of alternated series     *)
Theorem alternated_series :
  forall Un:nat -> R,
    Un_decreasing Un ->
    Un_cv Un 0 ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) N) l }.
Proof.
  intros; apply CV_ALT.
  assumption.
  unfold positivity_seq; apply decreasing_ineq; assumption.
  assumption.
Qed.

Theorem alternated_series_ineq :
  forall (Un:nat -> R) (l:R) (N:nat),
    Un_decreasing Un ->
    Un_cv Un 0 ->
    Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) N) l ->
    sum_f_R0 (tg_alt Un) (S (2 * N)) <= l <= sum_f_R0 (tg_alt Un) (2 * N).
Proof.
  intros.
  cut (Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) (2 * N)) l).
  cut (Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) (S (2 * N))) l).
  intros; split.
  apply (growing_ineq (fun N:nat => sum_f_R0 (tg_alt Un) (S (2 * N)))).
  apply CV_ALT_step0; assumption.
  assumption.
  apply (decreasing_ineq (fun N:nat => sum_f_R0 (tg_alt Un) (2 * N))).
  apply CV_ALT_step1; assumption.
  assumption.
  unfold Un_cv; unfold R_dist; unfold Un_cv in H1;
    unfold R_dist in H1; intros.
  elim (H1 eps H2); intros.
  exists x; intros.
  apply H3.
  unfold ge; apply le_trans with (2 * n)%nat.
  apply le_trans with n.
  assumption.
  assert (H5 := mult_O_le n 2).
  elim H5; intro.
  cut (0%nat <> 2%nat);
    [ intro; elim H7; symmetry ; assumption | discriminate ].
  assumption.
  apply le_n_Sn.
  unfold Un_cv; unfold R_dist; unfold Un_cv in H1;
    unfold R_dist in H1; intros.
  elim (H1 eps H2); intros.
  exists x; intros.
  apply H3.
  unfold ge; apply le_trans with n.
  assumption.
  assert (H5 := mult_O_le n 2).
  elim H5; intro.
  cut (0%nat <> 2%nat);
    [ intro; elim H7; symmetry ; assumption | discriminate ].
  assumption.
Qed.

(***************************************)
(** * Application : construction of PI *)
(***************************************)

Definition PI_tg (n:nat) := / INR (2 * n + 1).

Lemma PI_tg_pos : forall n:nat, 0 <= PI_tg n.
Proof.
  intro; unfold PI_tg; left; apply Rinv_0_lt_compat; apply lt_INR_0;
    replace (2 * n + 1)%nat with (S (2 * n)); [ apply lt_O_Sn | ring ].
Qed.

Lemma PI_tg_decreasing : Un_decreasing PI_tg.
Proof.
  unfold PI_tg, Un_decreasing; intro.
  apply Rmult_le_reg_l with (INR (2 * n + 1)).
  apply lt_INR_0.
  replace (2 * n + 1)%nat with (S (2 * n)); [ apply lt_O_Sn | ring ].
  rewrite <- Rinv_r_sym.
  apply Rmult_le_reg_l with (INR (2 * S n + 1)).
  apply lt_INR_0.
  replace (2 * S n + 1)%nat with (S (2 * S n)); [ apply lt_O_Sn | ring ].
  rewrite (Rmult_comm (INR (2 * S n + 1))); rewrite Rmult_assoc;
    rewrite <- Rinv_l_sym.
  do 2 rewrite Rmult_1_r; apply le_INR.
  replace (2 * S n + 1)%nat with (S (S (2 * n + 1))).
  apply le_trans with (S (2 * n + 1)); apply le_n_Sn.
  ring.
  apply not_O_INR; discriminate.
  apply not_O_INR; replace (2 * n + 1)%nat with (S (2 * n));
    [ discriminate | ring ].
Qed.

Lemma PI_tg_cv : Un_cv PI_tg 0.
Proof.
  unfold Un_cv; unfold R_dist; intros.
  cut (0 < 2 * eps);
    [ intro | apply Rmult_lt_0_compat; [ prove_sup0 | assumption ] ].
  assert (H1 := archimed (/ (2 * eps))).
  cut (0 <= up (/ (2 * eps)))%Z.
  intro; assert (H3 := IZN (up (/ (2 * eps))) H2).
  elim H3; intros N H4.
  cut (0 < N)%nat.
  intro; exists N; intros.
  cut (0 < n)%nat.
  intro; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r;
    rewrite Rabs_right.
  unfold PI_tg; apply Rlt_trans with (/ INR (2 * n)).
  apply Rmult_lt_reg_l with (INR (2 * n)).
  apply lt_INR_0.
  replace (2 * n)%nat with (n + n)%nat; [ idtac | ring ].
  apply lt_le_trans with n.
  assumption.
  apply le_plus_l.
  rewrite <- Rinv_r_sym.
  apply Rmult_lt_reg_l with (INR (2 * n + 1)).
  apply lt_INR_0.
  replace (2 * n + 1)%nat with (S (2 * n)); [ apply lt_O_Sn | ring ].
  rewrite (Rmult_comm (INR (2 * n + 1))).
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  do 2 rewrite Rmult_1_r; apply lt_INR.
  replace (2 * n + 1)%nat with (S (2 * n)); [ apply lt_n_Sn | ring ].
  apply not_O_INR; replace (2 * n + 1)%nat with (S (2 * n));
    [ discriminate | ring ].
  replace n with (S (pred n)).
  apply not_O_INR; discriminate.
  symmetry ; apply S_pred with 0%nat.
  assumption.
  apply Rle_lt_trans with (/ INR (2 * N)).
  apply Rinv_le_contravar.
  rewrite mult_INR; apply Rmult_lt_0_compat;
    [ simpl; prove_sup0 | apply lt_INR_0; assumption ].
  apply le_INR.
  now apply mult_le_compat_l.
  rewrite mult_INR.
  apply Rmult_lt_reg_l with (INR N / eps).
  apply Rdiv_lt_0_compat with (2 := H).
  now apply (lt_INR 0).
  replace (_ */ _) with (/(2 * eps)).
  replace (_ / _ * _) with (INR N).
  rewrite INR_IZR_INZ.
  now rewrite <- H4.
  field.
  now apply Rgt_not_eq.
  simpl (INR 2); field; split.
  now apply Rgt_not_eq, (lt_INR 0).
  now apply Rgt_not_eq.
  apply Rle_ge; apply PI_tg_pos.
  apply lt_le_trans with N; assumption.
  elim H1; intros H5 _.
  destruct (lt_eq_lt_dec 0 N) as [[| <- ]|H6].
  assumption.
  rewrite H4 in H5.
  simpl in H5.
  cut (0 < / (2 * eps)); [ intro | apply Rinv_0_lt_compat; assumption ].
  elim (Rlt_irrefl _ (Rlt_trans _ _ _ H6 H5)).
  elim (lt_n_O _ H6).
  apply le_IZR.
  left; apply Rlt_trans with (/ (2 * eps)).
  apply Rinv_0_lt_compat; assumption.
  elim H1; intros; assumption.
Qed.

Lemma exist_PI :
  { l:R | Un_cv (fun N:nat => sum_f_R0 (tg_alt PI_tg) N) l }.
Proof.
  apply alternated_series.
  apply PI_tg_decreasing.
  apply PI_tg_cv.
Qed.

(** Now, PI is defined *)
Definition Alt_PI : R := 4 * (let (a,_) := exist_PI in a).

(** We can get an approximation of PI with the following inequality *)
Lemma Alt_PI_ineq :
  forall N:nat,
    sum_f_R0 (tg_alt PI_tg) (S (2 * N)) <= Alt_PI / 4 <=
    sum_f_R0 (tg_alt PI_tg) (2 * N).
Proof.
  intro; apply alternated_series_ineq.
  apply PI_tg_decreasing.
  apply PI_tg_cv.
  unfold Alt_PI; case exist_PI; intro.
  replace (4 * x / 4) with x.
  trivial.
  unfold Rdiv; rewrite (Rmult_comm 4); rewrite Rmult_assoc;
    rewrite <- Rinv_r_sym; [ rewrite Rmult_1_r; reflexivity | discrR ].
Qed.

Lemma Alt_PI_RGT_0 : 0 < Alt_PI.
Proof.
  assert (H := Alt_PI_ineq 0).
  apply Rmult_lt_reg_l with (/ 4).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite Rmult_0_r; rewrite Rmult_comm.
  elim H; clear H; intros H _.
  unfold Rdiv in H;
    apply Rlt_le_trans with (sum_f_R0 (tg_alt PI_tg) (S (2 * 0))).
  simpl; unfold tg_alt; simpl; rewrite Rmult_1_l;
    rewrite Rmult_1_r; apply Rplus_lt_reg_l with (PI_tg 1).
  rewrite Rplus_0_r;
    replace (PI_tg 1 + (PI_tg 0 + -1 * PI_tg 1)) with (PI_tg 0);
      [ unfold PI_tg | ring ].
  simpl; apply Rinv_lt_contravar.
  rewrite Rmult_1_l; replace (2 + 1) with 3; [ prove_sup0 | ring ].
  rewrite Rplus_comm; pattern 1 at 1; rewrite <- Rplus_0_r;
    apply Rplus_lt_compat_l; prove_sup0.
  assumption.
Qed.
