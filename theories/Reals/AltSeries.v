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
Require Import Rseries.
Require Import SeqProp.
Require Import PartSum.
Require Import Max.
Open Local Scope R_scope.

(**********)
(** * Formalization of alternated series *)
Definition tg_alt (Un:nat -> R) (i:nat) : R := (-1) ^ i * Un i.
Definition positivity_seq (Un:nat -> R) : Prop := forall n:nat, 0 <= Un n.

Lemma CV_ALT_step0 :
  forall Un:nat -> R,
    Un_decreasing Un ->
    Un_growing (fun N:nat => sum_f_R0 (tg_alt Un) (S (2 * N))).
Proof.
  intros; unfold Un_growing in |- *; intro.
  cut ((2 * S n)%nat = S (S (2 * n))).
  intro; rewrite H0.
  do 4 rewrite tech5; repeat rewrite Rplus_assoc; apply Rplus_le_compat_l.
  pattern (tg_alt Un (S (2 * n))) at 1 in |- *; rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  unfold tg_alt in |- *; rewrite <- H0; rewrite pow_1_odd; rewrite pow_1_even;
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
  intros; unfold Un_decreasing in |- *; intro.
  cut ((2 * S n)%nat = S (S (2 * n))).
  intro; rewrite H0; do 2 rewrite tech5; repeat rewrite Rplus_assoc.
  pattern (sum_f_R0 (tg_alt Un) (2 * n)) at 2 in |- *; rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  unfold tg_alt in |- *; rewrite <- H0; rewrite pow_1_odd; rewrite pow_1_even;
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
  simpl in |- *; unfold tg_alt in |- *; simpl in |- *; rewrite Rmult_1_r.
  replace (-1 * -1 * Un 2%nat) with (Un 2%nat); [ idtac | ring ].
  apply Rplus_le_reg_l with (Un 1%nat); rewrite Rplus_0_r.
  replace (Un 1%nat + (-1 * Un 1%nat + Un 2%nat)) with (Un 2%nat);
    [ apply H | ring ].
  cut (S (2 * S N) = S (S (S (2 * N)))).
  intro; rewrite H1; do 2 rewrite tech5.
  apply Rle_trans with (sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * N))).
  pattern (sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * N))) at 2 in |- *;
    rewrite <- Rplus_0_r.
  rewrite Rplus_assoc; apply Rplus_le_compat_l.
  unfold tg_alt in |- *; rewrite <- H1.
  rewrite pow_1_odd.
  cut (S (S (2 * S N)) = (2 * S (S N))%nat).
  intro; rewrite H2; rewrite pow_1_even; rewrite Rmult_1_l; rewrite <- H2.
  apply Rplus_le_reg_l with (Un (S (2 * S N))).
  rewrite Rplus_0_r;
    replace (Un (S (2 * S N)) + (-1 * Un (S (2 * S N)) + Un (S (S (2 * S N)))))
      with (Un (S (S (2 * S N)))); [ idtac | ring ].
  apply H.
  ring_nat.
  apply HrecN.
  ring_nat.
Qed.

(** A more general inequality *)
Lemma CV_ALT_step3 :
  forall (Un:nat -> R) (N:nat),
    Un_decreasing Un ->
    positivity_seq Un -> sum_f_R0 (fun i:nat => tg_alt Un (S i)) N <= 0. 
Proof.
  intros; induction  N as [| N HrecN].
  simpl in |- *; unfold tg_alt in |- *; simpl in |- *; rewrite Rmult_1_r.
  apply Rplus_le_reg_l with (Un 1%nat).
  rewrite Rplus_0_r; replace (Un 1%nat + -1 * Un 1%nat) with 0;
    [ apply H0 | ring ].
  assert (H1 := even_odd_cor N).
  elim H1; intros.
  elim H2; intro.
  rewrite H3; apply CV_ALT_step2; assumption.
  rewrite H3; rewrite tech5.
  apply Rle_trans with (sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * x))).
  pattern (sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * x))) at 2 in |- *;
    rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  unfold tg_alt in |- *; simpl in |- *.
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
  intros; unfold has_ub in |- *; unfold bound in |- *.
  exists (Un 0%nat).
  unfold is_upper_bound in |- *; intros; elim H1; intros.
  rewrite H2; rewrite decomp_sum.
  replace (tg_alt Un 0) with (Un 0%nat).
  pattern (Un 0%nat) at 2 in |- *; rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  apply CV_ALT_step3; assumption.
  unfold tg_alt in |- *; simpl in |- *; ring.
  apply lt_O_Sn.
Qed.

(** This lemma gives an interesting result about alternated series *)
Lemma CV_ALT :
  forall Un:nat -> R,
    Un_decreasing Un ->
    positivity_seq Un ->
    Un_cv Un 0 ->
    sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) N) l).
Proof.
  intros.
  assert (H2 := CV_ALT_step0 _ H).
  assert (H3 := CV_ALT_step4 _ H H0).
  assert (X := growing_cv _ H2 H3).
  elim X; intros.
  apply existT with x.
  unfold Un_cv in |- *; unfold R_dist in |- *; unfold Un_cv in H1;
    unfold R_dist in H1; unfold Un_cv in p; unfold R_dist in p.
  intros; cut (0 < eps / 2);
    [ intro
      | unfold Rdiv in |- *; apply Rmult_lt_0_compat;
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
  rewrite Rabs_Ropp; unfold tg_alt in |- *; rewrite Rabs_mult;
    rewrite pow_1_abs; rewrite Rmult_1_l; unfold Rminus in H6;
      rewrite Ropp_0 in H6; rewrite <- (Rplus_0_r (Un (S n))); 
	apply H6.
  unfold ge in |- *; apply le_trans with n.
  apply le_trans with N; [ unfold N in |- *; apply le_max_r | assumption ].
  apply le_n_Sn.
  rewrite tech5; ring.
  rewrite H12; apply Rlt_trans with (eps / 2).
  apply H7; assumption.
  unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite (Rmult_comm 2); rewrite Rmult_assoc; rewrite <- Rinv_l_sym;
    [ rewrite Rmult_1_r | discrR ].
  rewrite double.
  pattern eps at 1 in |- *; rewrite <- (Rplus_0_r eps); apply Rplus_lt_compat_l;
    assumption.
  elim H10; intro; apply le_double.
  rewrite <- H11; apply le_trans with N.
  unfold N in |- *; apply le_trans with (S (2 * N1));
    [ apply le_n_Sn | apply le_max_l ].
  assumption.
  apply lt_n_Sm_le.
  rewrite <- H11.
  apply lt_le_trans with N.
  unfold N in |- *; apply lt_le_trans with (S (2 * N1)).
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
    sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) N) l).
Proof.
  intros; apply CV_ALT.
  assumption.
  unfold positivity_seq in |- *; apply decreasing_ineq; assumption.
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
  unfold Un_cv in |- *; unfold R_dist in |- *; unfold Un_cv in H1;
    unfold R_dist in H1; intros. 
  elim (H1 eps H2); intros.
  exists x; intros.
  apply H3.
  unfold ge in |- *; apply le_trans with (2 * n)%nat.
  apply le_trans with n.
  assumption.
  assert (H5 := mult_O_le n 2).
  elim H5; intro. 
  cut (0%nat <> 2%nat);
    [ intro; elim H7; symmetry  in |- *; assumption | discriminate ].
  assumption.
  apply le_n_Sn.
  unfold Un_cv in |- *; unfold R_dist in |- *; unfold Un_cv in H1;
    unfold R_dist in H1; intros. 
  elim (H1 eps H2); intros.
  exists x; intros.
  apply H3.
  unfold ge in |- *; apply le_trans with n.
  assumption.
  assert (H5 := mult_O_le n 2).
  elim H5; intro. 
  cut (0%nat <> 2%nat);
    [ intro; elim H7; symmetry  in |- *; assumption | discriminate ].
  assumption.
Qed.

(***************************************)
(** * Application : construction of PI *)
(***************************************)

Definition PI_tg (n:nat) := / INR (2 * n + 1).

Lemma PI_tg_pos : forall n:nat, 0 <= PI_tg n.
Proof.
  intro; unfold PI_tg in |- *; left; apply Rinv_0_lt_compat; apply lt_INR_0;
    replace (2 * n + 1)%nat with (S (2 * n)); [ apply lt_O_Sn | ring ].
Qed.

Lemma PI_tg_decreasing : Un_decreasing PI_tg.
Proof.
  unfold PI_tg, Un_decreasing in |- *; intro.
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
  ring_nat.
  apply not_O_INR; discriminate.
  apply not_O_INR; replace (2 * n + 1)%nat with (S (2 * n));
    [ discriminate | ring ].
Qed.

Lemma PI_tg_cv : Un_cv PI_tg 0.
Proof.
  unfold Un_cv in |- *; unfold R_dist in |- *; intros.
  cut (0 < 2 * eps);
    [ intro | apply Rmult_lt_0_compat; [ prove_sup0 | assumption ] ].
  assert (H1 := archimed (/ (2 * eps))).
  cut (0 <= up (/ (2 * eps)))%Z.
  intro; assert (H3 := IZN (up (/ (2 * eps))) H2).
  elim H3; intros N H4.
  cut (0 < N)%nat.
  intro; exists N; intros.
  cut (0 < n)%nat.
  intro; unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r;
    rewrite Rabs_right.
  unfold PI_tg in |- *; apply Rlt_trans with (/ INR (2 * n)).
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
  symmetry  in |- *; apply S_pred with 0%nat.
  assumption.
  apply Rle_lt_trans with (/ INR (2 * N)).
  apply Rmult_le_reg_l with (INR (2 * N)).
  rewrite mult_INR; apply Rmult_lt_0_compat;
    [ simpl in |- *; prove_sup0 | apply lt_INR_0; assumption ].
  rewrite <- Rinv_r_sym.
  apply Rmult_le_reg_l with (INR (2 * n)).
  rewrite mult_INR; apply Rmult_lt_0_compat;
    [ simpl in |- *; prove_sup0 | apply lt_INR_0; assumption ].
  rewrite (Rmult_comm (INR (2 * n))); rewrite Rmult_assoc;
    rewrite <- Rinv_l_sym.
  do 2 rewrite Rmult_1_r; apply le_INR.
  apply (fun m n p:nat => mult_le_compat_l p n m); assumption.
  replace n with (S (pred n)).
  apply not_O_INR; discriminate.
  symmetry  in |- *; apply S_pred with 0%nat.
  assumption.
  replace N with (S (pred N)).
  apply not_O_INR; discriminate.
  symmetry  in |- *; apply S_pred with 0%nat.
  assumption.
  rewrite mult_INR.
  rewrite Rinv_mult_distr.
  replace (INR 2) with 2; [ idtac | reflexivity ].
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym; [ idtac | discrR ].
  rewrite Rmult_1_l; apply Rmult_lt_reg_l with (INR N).
  apply lt_INR_0; assumption.
  rewrite <- Rinv_r_sym.
  apply Rmult_lt_reg_l with (/ (2 * eps)).
  apply Rinv_0_lt_compat; assumption.
  rewrite Rmult_1_r;
    replace (/ (2 * eps) * (INR N * (2 * eps))) with
      (INR N * (2 * eps * / (2 * eps))); [ idtac | ring ].
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; replace (INR N) with (IZR (Z_of_nat N)).
  rewrite <- H4.
  elim H1; intros; assumption.
  symmetry  in |- *; apply INR_IZR_INZ.
  apply prod_neq_R0;
    [ discrR | red in |- *; intro; rewrite H8 in H; elim (Rlt_irrefl _ H) ].
  apply not_O_INR.
  red in |- *; intro; rewrite H8 in H5; elim (lt_irrefl _ H5).
  replace (INR 2) with 2; [ discrR | reflexivity ].
  apply not_O_INR.
  red in |- *; intro; rewrite H8 in H5; elim (lt_irrefl _ H5).
  apply Rle_ge; apply PI_tg_pos.
  apply lt_le_trans with N; assumption.
  elim H1; intros H5 _.
  assert (H6 := lt_eq_lt_dec 0 N).
  elim H6; intro.
  elim a; intro.
  assumption.
  rewrite <- b in H4.
  rewrite H4 in H5.
  simpl in H5.
  cut (0 < / (2 * eps)); [ intro | apply Rinv_0_lt_compat; assumption ].
  elim (Rlt_irrefl _ (Rlt_trans _ _ _ H7 H5)).
  elim (lt_n_O _ b).
  apply le_IZR.
  simpl in |- *.
  left; apply Rlt_trans with (/ (2 * eps)).
  apply Rinv_0_lt_compat; assumption.
  elim H1; intros; assumption.
Qed.

Lemma exist_PI :
  sigT (fun l:R => Un_cv (fun N:nat => sum_f_R0 (tg_alt PI_tg) N) l).
Proof.
  apply alternated_series.
  apply PI_tg_decreasing.
  apply PI_tg_cv.
Qed.

(** Now, PI is defined *)
Definition PI : R := 4 * match exist_PI with
                           | existT a b => a
                         end.

(** We can get an approximation of PI with the following inequality *)
Lemma PI_ineq :
  forall N:nat,
    sum_f_R0 (tg_alt PI_tg) (S (2 * N)) <= PI / 4 <=
    sum_f_R0 (tg_alt PI_tg) (2 * N).
Proof.
  intro; apply alternated_series_ineq.
  apply PI_tg_decreasing.
  apply PI_tg_cv.
  unfold PI in |- *; case exist_PI; intro.
  replace (4 * x / 4) with x.
  trivial.
  unfold Rdiv in |- *; rewrite (Rmult_comm 4); rewrite Rmult_assoc;
    rewrite <- Rinv_r_sym; [ rewrite Rmult_1_r; reflexivity | discrR ].
Qed.

Lemma PI_RGT_0 : 0 < PI.
Proof.
  assert (H := PI_ineq 0).
  apply Rmult_lt_reg_l with (/ 4).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite Rmult_0_r; rewrite Rmult_comm.
  elim H; clear H; intros H _.
  unfold Rdiv in H;
    apply Rlt_le_trans with (sum_f_R0 (tg_alt PI_tg) (S (2 * 0))).
  simpl in |- *; unfold tg_alt in |- *; simpl in |- *; rewrite Rmult_1_l;
    rewrite Rmult_1_r; apply Rplus_lt_reg_r with (PI_tg 1).
  rewrite Rplus_0_r;
    replace (PI_tg 1 + (PI_tg 0 + -1 * PI_tg 1)) with (PI_tg 0);
      [ unfold PI_tg in |- * | ring ].
  simpl in |- *; apply Rinv_lt_contravar.
  rewrite Rmult_1_l; replace (2 + 1) with 3; [ prove_sup0 | ring ].
  rewrite Rplus_comm; pattern 1 at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_lt_compat_l; prove_sup0.
  assumption.
Qed.
