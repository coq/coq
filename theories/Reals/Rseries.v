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
Require Import Classical.
Require Import Compare.
Open Local Scope R_scope.

Implicit Type r : R.

(* classical is needed for [Un_cv_crit] *)
(*********************************************************)
(** *        Definition of sequence and properties       *)
(*                                                       *)
(*********************************************************)

Section sequence.

(*********)
  Variable Un : nat -> R.

(*********)
  Boxed Fixpoint Rmax_N (N:nat) : R :=
    match N with
      | O => Un 0
      | S n => Rmax (Un (S n)) (Rmax_N n)
    end.

(*********)
  Definition EUn r : Prop :=  exists i : nat, r = Un i.

(*********)
  Definition Un_cv (l:R) : Prop :=
    forall eps:R,
      eps > 0 ->
      exists N : nat, (forall n:nat, (n >= N)%nat -> R_dist (Un n) l < eps).

(*********)
  Definition Cauchy_crit : Prop :=
    forall eps:R,
      eps > 0 ->
      exists N : nat,
        (forall n m:nat,
          (n >= N)%nat -> (m >= N)%nat -> R_dist (Un n) (Un m) < eps).

(*********)
  Definition Un_growing : Prop := forall n:nat, Un n <= Un (S n).

(*********)
  Lemma EUn_noempty :  exists r : R, EUn r.
  Proof.
    unfold EUn in |- *; split with (Un 0); split with 0%nat; trivial.
  Qed.

(*********)
  Lemma Un_in_EUn : forall n:nat, EUn (Un n).
  Proof.
    intro; unfold EUn in |- *; split with n; trivial.
  Qed.

(*********)
  Lemma Un_bound_imp :
    forall x:R, (forall n:nat, Un n <= x) -> is_upper_bound EUn x.
  Proof.
    intros; unfold is_upper_bound in |- *; intros; unfold EUn in H0; elim H0;
      clear H0; intros; generalize (H x1); intro; rewrite <- H0 in H1;
        trivial.
  Qed.

(*********)
  Lemma growing_prop :
    forall n m:nat, Un_growing -> (n >= m)%nat -> Un n >= Un m.
  Proof.
    double induction n m; intros.
    unfold Rge in |- *; right; trivial.
    exfalso; unfold ge in H1; generalize (le_Sn_O n0); intro; auto.
    cut (n0 >= 0)%nat.
    generalize H0; intros; unfold Un_growing in H0;
      apply
        (Rge_trans (Un (S n0)) (Un n0) (Un 0) (Rle_ge (Un n0) (Un (S n0)) (H0 n0))
          (H 0%nat H2 H3)).
    elim n0; auto.
    elim (lt_eq_lt_dec n1 n0); intro y.
    elim y; clear y; intro y.
    unfold ge in H2; generalize (le_not_lt n0 n1 (le_S_n n0 n1 H2)); intro;
      exfalso; auto.
    rewrite y; unfold Rge in |- *; right; trivial.
    unfold ge in H0; generalize (H0 (S n0) H1 (lt_le_S n0 n1 y)); intro;
      unfold Un_growing in H1;
        apply
          (Rge_trans (Un (S n1)) (Un n1) (Un (S n0))
            (Rle_ge (Un n1) (Un (S n1)) (H1 n1)) H3).
  Qed.


(** classical is needed: [not_all_not_ex] *)
(*********)
  Lemma Un_cv_crit : Un_growing -> bound EUn ->  exists l : R, Un_cv l.
  Proof.
    unfold Un_growing, Un_cv in |- *; intros;
      generalize (completeness_weak EUn H0 EUn_noempty);
        intro; elim H1; clear H1; intros; split with x; intros;
          unfold is_lub in H1; unfold bound in H0; unfold is_upper_bound in H0, H1;
            elim H0; clear H0; intros; elim H1; clear H1; intros;
              generalize (H3 x0 H0); intro; cut (forall n:nat, Un n <= x);
                intro.
    cut (exists N : nat, x - eps < Un N).
    intro; elim H6; clear H6; intros; split with x1.
    intros; unfold R_dist in |- *; apply (Rabs_def1 (Un n - x) eps).
    unfold Rgt in H2;
      apply (Rle_lt_trans (Un n - x) 0 eps (Rle_minus (Un n) x (H5 n)) H2).
    fold Un_growing in H; generalize (growing_prop n x1 H H7); intro;
      generalize
        (Rlt_le_trans (x - eps) (Un x1) (Un n) H6 (Rge_le (Un n) (Un x1) H8));
        intro; generalize (Rplus_lt_compat_l (- x) (x - eps) (Un n) H9);
          unfold Rminus in |- *; rewrite <- (Rplus_assoc (- x) x (- eps));
            rewrite (Rplus_comm (- x) (Un n)); fold (Un n - x) in |- *;
              rewrite Rplus_opp_l; rewrite (let (H1, H2) := Rplus_ne (- eps) in H2);
                trivial.
    cut (~ (forall N:nat, x - eps >= Un N)).
    intro; apply (not_all_not_ex nat (fun N:nat => x - eps < Un N)); red in |- *;
      intro; red in H6; elim H6; clear H6; intro;
        apply (Rnot_lt_ge (x - eps) (Un N) (H7 N)).
    red in |- *; intro; cut (forall N:nat, Un N <= x - eps).
    intro; generalize (Un_bound_imp (x - eps) H7); intro;
      unfold is_upper_bound in H8; generalize (H3 (x - eps) H8);
        intro; generalize (Rle_minus x (x - eps) H9); unfold Rminus in |- *;
          rewrite Ropp_plus_distr; rewrite <- Rplus_assoc; rewrite Rplus_opp_r;
            rewrite (let (H1, H2) := Rplus_ne (- - eps) in H2);
              rewrite Ropp_involutive; intro; unfold Rgt in H2;
                generalize (Rgt_not_le eps 0 H2); intro; auto.
    intro; elim (H6 N); intro; unfold Rle in |- *.
    left; unfold Rgt in H7; assumption.
    right; auto.
    apply (H1 (Un n) (Un_in_EUn n)).
  Qed.

(*********)
  Lemma finite_greater :
    forall N:nat,  exists M : R, (forall n:nat, (n <= N)%nat -> Un n <= M).
  Proof.
    intro; induction  N as [| N HrecN].
    split with (Un 0); intros; rewrite (le_n_O_eq n H);
      apply (Req_le (Un n) (Un n) (refl_equal (Un n))).
    elim HrecN; clear HrecN; intros; split with (Rmax (Un (S N)) x); intros;
      elim (Rmax_Rle (Un (S N)) x (Un n)); intros; clear H1;
        inversion H0.
    rewrite <- H1; rewrite <- H1 in H2;
      apply
        (H2 (or_introl (Un n <= x) (Req_le (Un n) (Un n) (refl_equal (Un n))))).
    apply (H2 (or_intror (Un n <= Un (S N)) (H n H3))).
  Qed.

(*********)
  Lemma cauchy_bound : Cauchy_crit -> bound EUn.
  Proof.
    unfold Cauchy_crit, bound in |- *; intros; unfold is_upper_bound in |- *;
      unfold Rgt in H; elim (H 1 Rlt_0_1); clear H; intros;
        generalize (H x); intro; generalize (le_dec x); intro;
          elim (finite_greater x); intros; split with (Rmax x0 (Un x + 1));
            clear H; intros; unfold EUn in H; elim H; clear H;
              intros; elim (H1 x2); clear H1; intro y.
    unfold ge in H0; generalize (H0 x2 (le_n x) y); clear H0; intro;
      rewrite <- H in H0; unfold R_dist in H0; elim (Rabs_def2 (Un x - x1) 1 H0);
        clear H0; intros; elim (Rmax_Rle x0 (Un x + 1) x1);
          intros; apply H4; clear H3 H4; right; clear H H0 y;
            apply (Rlt_le x1 (Un x + 1)); generalize (Rlt_minus (-1) (Un x - x1) H1);
              clear H1; intro; apply (Rminus_lt x1 (Un x + 1));
                cut (-1 - (Un x - x1) = x1 - (Un x + 1));
                  [ intro; rewrite H0 in H; assumption | ring ].
    generalize (H2 x2 y); clear H2 H0; intro; rewrite <- H in H0;
      elim (Rmax_Rle x0 (Un x + 1) x1); intros; clear H1;
        apply H2; left; assumption.
  Qed.

End sequence.

(*****************************************************************)
(**  *       Definition of Power Series and properties           *)
(*                                                               *)
(*****************************************************************)

Section Isequence.

(*********)
  Variable An : nat -> R.

(*********)
  Definition Pser (x l:R) : Prop := infinite_sum (fun n:nat => An n * x ^ n) l.

End Isequence.

Lemma GP_infinite :
  forall x:R, Rabs x < 1 -> Pser (fun n:nat => 1) x (/ (1 - x)).
Proof.
  intros; unfold Pser in |- *; unfold infinite_sum in |- *; intros;
    elim (Req_dec x 0).
  intros; exists 0%nat; intros; rewrite H1; rewrite Rminus_0_r; rewrite Rinv_1;
    cut (sum_f_R0 (fun n0:nat => 1 * 0 ^ n0) n = 1).
  intros; rewrite H3; rewrite R_dist_eq; auto.
  elim n; simpl in |- *.
  ring.
  intros; rewrite H3; ring.
  intro; cut (0 < eps * (Rabs (1 - x) * Rabs (/ x))).
  intro; elim (pow_lt_1_zero x H (eps * (Rabs (1 - x) * Rabs (/ x))) H2);
    intro N; intros; exists N; intros;
      cut
        (sum_f_R0 (fun n0:nat => 1 * x ^ n0) n = sum_f_R0 (fun n0:nat => x ^ n0) n).
  intros; rewrite H5;
    apply
      (Rmult_lt_reg_l (Rabs (1 - x))
        (R_dist (sum_f_R0 (fun n0:nat => x ^ n0) n) (/ (1 - x))) eps).
  apply Rabs_pos_lt.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt in |- *.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  unfold R_dist in |- *; rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_l.
  cut
    ((1 - x) * sum_f_R0 (fun n0:nat => x ^ n0) n =
      - (sum_f_R0 (fun n0:nat => x ^ n0) n * (x - 1))).
  intro; rewrite H6.
  rewrite GP_finite.
  rewrite Rinv_r.
  cut (- (x ^ (n + 1) - 1) - 1 = - x ^ (n + 1)).
  intro; rewrite H7.
  rewrite Rabs_Ropp; cut ((n + 1)%nat = S n); auto.
  intro H8; rewrite H8; simpl in |- *; rewrite Rabs_mult;
    apply
      (Rlt_le_trans (Rabs x * Rabs (x ^ n))
        (Rabs x * (eps * (Rabs (1 - x) * Rabs (/ x)))) (
          Rabs (1 - x) * eps)).
  apply Rmult_lt_compat_l.
  apply Rabs_pos_lt.
  assumption.
  auto.
  cut
    (Rabs x * (eps * (Rabs (1 - x) * Rabs (/ x))) =
      Rabs x * Rabs (/ x) * (eps * Rabs (1 - x))).
  clear H8; intros; rewrite H8; rewrite <- Rabs_mult; rewrite Rinv_r.
  rewrite Rabs_R1; cut (1 * (eps * Rabs (1 - x)) = Rabs (1 - x) * eps).
  intros; rewrite H9; unfold Rle in |- *; right; reflexivity.
  ring.
  assumption.
  ring.
  ring.
  ring.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt in |- *.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  ring; ring.
  elim n; simpl in |- *.
  ring.
  intros; rewrite H5.
  ring.
  apply Rmult_lt_0_compat.
  auto.
  apply Rmult_lt_0_compat.
  apply Rabs_pos_lt.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt in |- *.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  apply Rabs_pos_lt.
  apply Rinv_neq_0_compat.
  assumption.
Qed.
