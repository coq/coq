(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Sumbool.
Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Ranalysis1.
Open Local Scope R_scope.

Boxed Fixpoint Dichotomy_lb (x y:R) (P:R -> bool) (N:nat) {struct N} : R :=
  match N with
    | O => x
    | S n =>
      let down := Dichotomy_lb x y P n in
        let up := Dichotomy_ub x y P n in
          let z := (down + up) / 2 in if P z then down else z
  end

  with Dichotomy_ub (x y:R) (P:R -> bool) (N:nat) {struct N} : R :=
    match N with
      | O => y
      | S n =>
        let down := Dichotomy_lb x y P n in
          let up := Dichotomy_ub x y P n in
            let z := (down + up) / 2 in if P z then z else up
    end.

Definition dicho_lb (x y:R) (P:R -> bool) (N:nat) : R := Dichotomy_lb x y P N.
Definition dicho_up (x y:R) (P:R -> bool) (N:nat) : R := Dichotomy_ub x y P N.

(**********)
Lemma dicho_comp :
  forall (x y:R) (P:R -> bool) (n:nat),
    x <= y -> dicho_lb x y P n <= dicho_up x y P n.
Proof.
  intros.
  induction  n as [| n Hrecn].
  simpl in |- *; assumption.
  simpl in |- *.
  case (P ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2)).
  unfold Rdiv in |- *; apply Rmult_le_reg_l with 2.
  prove_sup0.
  pattern 2 at 1 in |- *; rewrite Rmult_comm.
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym; [ idtac | discrR ].
  rewrite Rmult_1_r.
  rewrite double.
  apply Rplus_le_compat_l.
  assumption.
  unfold Rdiv in |- *; apply Rmult_le_reg_l with 2.
  prove_sup0.
  pattern 2 at 3 in |- *; rewrite Rmult_comm.
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym; [ idtac | discrR ].
  rewrite Rmult_1_r.
  rewrite double.
  rewrite <- (Rplus_comm (Dichotomy_ub x y P n)).
  apply Rplus_le_compat_l.
  assumption.
Qed.

Lemma dicho_lb_growing :
  forall (x y:R) (P:R -> bool), x <= y -> Un_growing (dicho_lb x y P).
Proof.
  intros.
  unfold Un_growing in |- *.
  intro.
  simpl in |- *.
  case (P ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2)).
  right; reflexivity.
  unfold Rdiv in |- *; apply Rmult_le_reg_l with 2.
  prove_sup0.
  pattern 2 at 1 in |- *; rewrite Rmult_comm.
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym; [ idtac | discrR ].
  rewrite Rmult_1_r.
  rewrite double.
  apply Rplus_le_compat_l.
  replace (Dichotomy_ub x y P n) with (dicho_up x y P n);
  [ apply dicho_comp; assumption | reflexivity ].
Qed.

Lemma dicho_up_decreasing :
  forall (x y:R) (P:R -> bool), x <= y -> Un_decreasing (dicho_up x y P).
Proof.
  intros.
  unfold Un_decreasing in |- *.
  intro.
  simpl in |- *.
  case (P ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2)).
  unfold Rdiv in |- *; apply Rmult_le_reg_l with 2.
  prove_sup0.
  pattern 2 at 3 in |- *; rewrite Rmult_comm.
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym; [ idtac | discrR ].
  rewrite Rmult_1_r.
  rewrite double.
  replace (Dichotomy_ub x y P n) with (dicho_up x y P n);
  [ idtac | reflexivity ].
  replace (Dichotomy_lb x y P n) with (dicho_lb x y P n);
  [ idtac | reflexivity ].
  rewrite <- (Rplus_comm (dicho_up x y P n)).
  apply Rplus_le_compat_l.
  apply dicho_comp; assumption.
  right; reflexivity.
Qed.

Lemma dicho_lb_maj_y :
  forall (x y:R) (P:R -> bool), x <= y -> forall n:nat, dicho_lb x y P n <= y.
Proof.
  intros.
  induction  n as [| n Hrecn].
  simpl in |- *; assumption.
  simpl in |- *.
  case (P ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2)).
  assumption.
  unfold Rdiv in |- *; apply Rmult_le_reg_l with 2.
  prove_sup0.
  pattern 2 at 3 in |- *; rewrite Rmult_comm.
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym; [ rewrite Rmult_1_r | discrR ].
  rewrite double; apply Rplus_le_compat.
  assumption.
  pattern y at 2 in |- *; replace y with (Dichotomy_ub x y P 0);
    [ idtac | reflexivity ].
  apply decreasing_prop.
  assert (H0 := dicho_up_decreasing x y P H).
  assumption.
  apply le_O_n.
Qed.

Lemma dicho_lb_maj :
  forall (x y:R) (P:R -> bool), x <= y -> has_ub (dicho_lb x y P).
Proof.
  intros.
  cut (forall n:nat, dicho_lb x y P n <= y).
  intro.
  unfold has_ub in |- *.
  unfold bound in |- *.
  exists y.
  unfold is_upper_bound in |- *.
  intros.
  elim H1; intros.
  rewrite H2; apply H0.
  apply dicho_lb_maj_y; assumption.
Qed.

Lemma dicho_up_min_x :
  forall (x y:R) (P:R -> bool), x <= y -> forall n:nat, x <= dicho_up x y P n.
Proof.
  intros.
  induction  n as [| n Hrecn].
  simpl in |- *; assumption.
  simpl in |- *.
  case (P ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2)).
  unfold Rdiv in |- *; apply Rmult_le_reg_l with 2.
  prove_sup0.
  pattern 2 at 1 in |- *; rewrite Rmult_comm.
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym; [ rewrite Rmult_1_r | discrR ].
  rewrite double; apply Rplus_le_compat.
  pattern x at 1 in |- *; replace x with (Dichotomy_lb x y P 0);
    [ idtac | reflexivity ].
  apply tech9.
  assert (H0 := dicho_lb_growing x y P H).
  assumption.
  apply le_O_n.
  assumption.
  assumption.
Qed.

Lemma dicho_up_min :
  forall (x y:R) (P:R -> bool), x <= y -> has_lb (dicho_up x y P).
Proof.
  intros.
  cut (forall n:nat, x <= dicho_up x y P n).
  intro.
  unfold has_lb in |- *.
  unfold bound in |- *.
  exists (- x).
  unfold is_upper_bound in |- *.
  intros.
  elim H1; intros.
  rewrite H2.
  unfold opp_seq in |- *.
  apply Ropp_le_contravar.
  apply H0.
  apply dicho_up_min_x; assumption.
Qed.

Lemma dicho_lb_cv :
  forall (x y:R) (P:R -> bool),
    x <= y -> { l:R | Un_cv (dicho_lb x y P) l }.
Proof.
  intros.
  apply growing_cv.
  apply dicho_lb_growing; assumption.
  apply dicho_lb_maj; assumption.
Qed.

Lemma dicho_up_cv :
  forall (x y:R) (P:R -> bool),
    x <= y -> { l:R | Un_cv (dicho_up x y P) l }.
Proof.
  intros.
  apply decreasing_cv.
  apply dicho_up_decreasing; assumption.
  apply dicho_up_min; assumption.
Qed.

Lemma dicho_lb_dicho_up :
  forall (x y:R) (P:R -> bool) (n:nat),
    x <= y -> dicho_up x y P n - dicho_lb x y P n = (y - x) / 2 ^ n.
Proof.
  intros.
  induction  n as [| n Hrecn].
  simpl in |- *.
  unfold Rdiv in |- *; rewrite Rinv_1; ring.
  simpl in |- *.
  case (P ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2)).
  unfold Rdiv in |- *.
  replace
  ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) * / 2 - Dichotomy_lb x y P n)
    with ((dicho_up x y P n - dicho_lb x y P n) / 2).
  unfold Rdiv in |- *; rewrite Hrecn.
  unfold Rdiv in |- *.
  rewrite Rinv_mult_distr.
  ring.
  discrR.
  apply pow_nonzero; discrR.
  pattern (Dichotomy_lb x y P n) at 2 in |- *;
    rewrite (double_var (Dichotomy_lb x y P n));
      unfold dicho_up, dicho_lb, Rminus, Rdiv in |- *; ring.
  replace
  (Dichotomy_ub x y P n - (Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2)
    with ((dicho_up x y P n - dicho_lb x y P n) / 2).
  unfold Rdiv in |- *; rewrite Hrecn.
  unfold Rdiv in |- *.
  rewrite Rinv_mult_distr.
  ring.
  discrR.
  apply pow_nonzero; discrR.
  pattern (Dichotomy_ub x y P n) at 1 in |- *;
    rewrite (double_var (Dichotomy_ub x y P n));
      unfold dicho_up, dicho_lb, Rminus, Rdiv in |- *; ring.
Qed.

Definition pow_2_n (n:nat) := 2 ^ n.

Lemma pow_2_n_neq_R0 : forall n:nat, pow_2_n n <> 0.
Proof.
  intro.
  unfold pow_2_n in |- *.
  apply pow_nonzero.
  discrR.
Qed.

Lemma pow_2_n_growing : Un_growing pow_2_n.
Proof.
  unfold Un_growing in |- *.
  intro.
  replace (S n) with (n + 1)%nat;
  [ unfold pow_2_n in |- *; rewrite pow_add | ring ].
  pattern (2 ^ n) at 1 in |- *; rewrite <- Rmult_1_r.
  apply Rmult_le_compat_l.
  left; apply pow_lt; prove_sup0.
  simpl in |- *.
  rewrite Rmult_1_r.
  pattern 1 at 1 in |- *; rewrite <- Rplus_0_r; apply Rplus_le_compat_l; left;
    apply Rlt_0_1.
Qed.

Lemma pow_2_n_infty : cv_infty pow_2_n.
Proof.
  cut (forall N:nat, INR N <= 2 ^ N).
  intros.
  unfold cv_infty in |- *.
  intro.
  case (total_order_T 0 M); intro.
  elim s; intro.
  set (N := up M).
  cut (0 <= N)%Z.
  intro.
  elim (IZN N H0); intros N0 H1.
  exists N0.
  intros.
  apply Rlt_le_trans with (INR N0).
  rewrite INR_IZR_INZ.
  rewrite <- H1.
  unfold N in |- *.
  assert (H3 := archimed M).
  elim H3; intros; assumption.
  apply Rle_trans with (pow_2_n N0).
  unfold pow_2_n in |- *; apply H.
  apply Rge_le.
  apply growing_prop.
  apply pow_2_n_growing.
  assumption.
  apply le_IZR.
  unfold N in |- *.
  simpl in |- *.
  assert (H0 := archimed M); elim H0; intros.
  left; apply Rlt_trans with M; assumption.
  exists 0%nat; intros.
  rewrite <- b.
  unfold pow_2_n in |- *; apply pow_lt; prove_sup0.
  exists 0%nat; intros.
  apply Rlt_trans with 0.
  assumption.
  unfold pow_2_n in |- *; apply pow_lt; prove_sup0.
  simple induction N.
  simpl in |- *.
  left; apply Rlt_0_1.
  intros.
  pattern (S n) at 2 in |- *; replace (S n) with (n + 1)%nat; [ idtac | ring ].
  rewrite S_INR; rewrite pow_add.
  simpl in |- *.
  rewrite Rmult_1_r.
  apply Rle_trans with (2 ^ n).
  rewrite <- (Rplus_comm 1).
  rewrite <- (Rmult_1_r (INR n)).
  apply (poly n 1).
  apply Rlt_0_1.
  pattern (2 ^ n) at 1 in |- *; rewrite <- Rplus_0_r.
  rewrite <- (Rmult_comm 2).
  rewrite double.
  apply Rplus_le_compat_l.
  left; apply pow_lt; prove_sup0.
Qed.

Lemma cv_dicho :
  forall (x y l1 l2:R) (P:R -> bool),
    x <= y ->
    Un_cv (dicho_lb x y P) l1 -> Un_cv (dicho_up x y P) l2 -> l1 = l2.
Proof.
  intros.
  assert (H2 := CV_minus _ _ _ _ H0 H1).
  cut (Un_cv (fun i:nat => dicho_lb x y P i - dicho_up x y P i) 0).
  intro.
  assert (H4 := UL_sequence _ _ _ H2 H3).
  symmetry  in |- *; apply Rminus_diag_uniq_sym; assumption.
  unfold Un_cv in |- *; unfold R_dist in |- *.
  intros.
  assert (H4 := cv_infty_cv_R0 pow_2_n pow_2_n_neq_R0 pow_2_n_infty).
  case (total_order_T x y); intro.
  elim s; intro.
  unfold Un_cv in H4; unfold R_dist in H4.
  cut (0 < y - x).
  intro Hyp.
  cut (0 < eps / (y - x)).
  intro.
  elim (H4 (eps / (y - x)) H5); intros N H6.
  exists N; intros.
  replace (dicho_lb x y P n - dicho_up x y P n - 0) with
  (dicho_lb x y P n - dicho_up x y P n); [ idtac | ring ].
  rewrite <- Rabs_Ropp.
  rewrite Ropp_minus_distr'.
  rewrite dicho_lb_dicho_up.
  unfold Rdiv in |- *; rewrite Rabs_mult.
  rewrite (Rabs_right (y - x)).
  apply Rmult_lt_reg_l with (/ (y - x)).
  apply Rinv_0_lt_compat; assumption.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l.
  replace (/ 2 ^ n) with (/ 2 ^ n - 0);
  [ unfold pow_2_n, Rdiv in H6; rewrite <- (Rmult_comm eps); apply H6;
    assumption
    | ring ].
  red in |- *; intro; rewrite H8 in Hyp; elim (Rlt_irrefl _ Hyp).
  apply Rle_ge.
  apply Rplus_le_reg_l with x; rewrite Rplus_0_r.
  replace (x + (y - x)) with y; [ assumption | ring ].
  assumption.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; assumption ].
  apply Rplus_lt_reg_r with x; rewrite Rplus_0_r.
  replace (x + (y - x)) with y; [ assumption | ring ].
  exists 0%nat; intros.
  replace (dicho_lb x y P n - dicho_up x y P n - 0) with
  (dicho_lb x y P n - dicho_up x y P n); [ idtac | ring ].
  rewrite <- Rabs_Ropp.
  rewrite Ropp_minus_distr'.
  rewrite dicho_lb_dicho_up.
  rewrite b.
  unfold Rminus, Rdiv in |- *; rewrite Rplus_opp_r; rewrite Rmult_0_l;
    rewrite Rabs_R0; assumption.
  assumption.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H r)).
Qed.

Definition cond_positivity (x:R) : bool :=
  match Rle_dec 0 x with
    | left _ => true
    | right _ => false
  end.

(** Sequential caracterisation of continuity *)
Lemma continuity_seq :
  forall (f:R -> R) (Un:nat -> R) (l:R),
    continuity_pt f l -> Un_cv Un l -> Un_cv (fun i:nat => f (Un i)) (f l).
Proof.
  unfold continuity_pt, Un_cv in |- *; unfold continue_in in |- *.
  unfold limit1_in in |- *.
  unfold limit_in in |- *.
  unfold dist in |- *.
  simpl in |- *.
  unfold R_dist in |- *.
  intros.
  elim (H eps H1); intros alp H2.
  elim H2; intros.
  elim (H0 alp H3); intros N H5.
  exists N; intros.
  case (Req_dec (Un n) l); intro.
  rewrite H7; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
    assumption.
  apply H4.
  split.
  unfold D_x, no_cond in |- *.
  split.
  trivial.
  apply (sym_not_eq (A:=R)); assumption.
  apply H5; assumption.
Qed.

Lemma dicho_lb_car :
  forall (x y:R) (P:R -> bool) (n:nat),
    P x = false -> P (dicho_lb x y P n) = false.
Proof.
  intros.
  induction  n as [| n Hrecn].
  simpl in |- *.
  assumption.
  simpl in |- *.
  assert
    (X :=
      sumbool_of_bool (P ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2))).
  elim X; intro.
  rewrite a.
  unfold dicho_lb in Hrecn; assumption.
  rewrite b.
  assumption.
Qed.

Lemma dicho_up_car :
  forall (x y:R) (P:R -> bool) (n:nat),
    P y = true -> P (dicho_up x y P n) = true.
Proof.
  intros.
  induction  n as [| n Hrecn].
  simpl in |- *.
  assumption.
  simpl in |- *.
  assert
    (X :=
      sumbool_of_bool (P ((Dichotomy_lb x y P n + Dichotomy_ub x y P n) / 2))).
  elim X; intro.
  rewrite a.
  unfold dicho_lb in Hrecn; assumption.
  rewrite b.
  assumption.
Qed.

(** Intermediate Value Theorem *)
Lemma IVT :
  forall (f:R -> R) (x y:R),
    continuity f ->
    x < y -> f x < 0 -> 0 < f y -> { z:R | x <= z <= y /\ f z = 0 }.
Proof.
  intros.
  cut (x <= y).
  intro.
  generalize (dicho_lb_cv x y (fun z:R => cond_positivity (f z)) H3).
  generalize (dicho_up_cv x y (fun z:R => cond_positivity (f z)) H3).
  intros X X0.
  elim X; intros.
  elim X0; intros.
  assert (H4 := cv_dicho _ _ _ _ _ H3 p0 p).
  rewrite H4 in p0.
  exists x0.
  split.
  split.
  apply Rle_trans with (dicho_lb x y (fun z:R => cond_positivity (f z)) 0).
  simpl in |- *.
  right; reflexivity.
  apply growing_ineq.
  apply dicho_lb_growing; assumption.
  assumption.
  apply Rle_trans with (dicho_up x y (fun z:R => cond_positivity (f z)) 0).
  apply decreasing_ineq.
  apply dicho_up_decreasing; assumption.
  assumption.
  right; reflexivity.
  2: left; assumption.
  set (Vn := fun n:nat => dicho_lb x y (fun z:R => cond_positivity (f z)) n).
  set (Wn := fun n:nat => dicho_up x y (fun z:R => cond_positivity (f z)) n).
  cut ((forall n:nat, f (Vn n) <= 0) -> f x0 <= 0).
  cut ((forall n:nat, 0 <= f (Wn n)) -> 0 <= f x0).
  intros.
  cut (forall n:nat, f (Vn n) <= 0).
  cut (forall n:nat, 0 <= f (Wn n)).
  intros.
  assert (H9 := H6 H8).
  assert (H10 := H5 H7).
  apply Rle_antisym; assumption.
  intro.
  unfold Wn in |- *.
  cut (forall z:R, cond_positivity z = true <-> 0 <= z).
  intro.
  assert (H8 := dicho_up_car x y (fun z:R => cond_positivity (f z)) n).
  elim (H7 (f (dicho_up x y (fun z:R => cond_positivity (f z)) n))); intros.
  apply H9.
  apply H8.
  elim (H7 (f y)); intros.
  apply H12.
  left; assumption.
  intro.
  unfold cond_positivity in |- *.
  case (Rle_dec 0 z); intro.
  split.
  intro; assumption.
  intro; reflexivity.
  split.
  intro feqt;discriminate feqt.
  intro.
  elim n0; assumption.
  unfold Vn in |- *.
  cut (forall z:R, cond_positivity z = false <-> z < 0).
  intros.
  assert (H8 := dicho_lb_car x y (fun z:R => cond_positivity (f z)) n).
  left.
  elim (H7 (f (dicho_lb x y (fun z:R => cond_positivity (f z)) n))); intros.
  apply H9.
  apply H8.
  elim (H7 (f x)); intros.
  apply H12.
  assumption.
  intro.
  unfold cond_positivity in |- *.
  case (Rle_dec 0 z); intro.
  split.
  intro feqt; discriminate feqt.
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r H7)).
  split.
  intro; auto with real.
  intro; reflexivity.
  cut (Un_cv Wn x0).
  intros.
  assert (H7 := continuity_seq f Wn x0 (H x0) H5).
  case (total_order_T 0 (f x0)); intro.
  elim s; intro.
  left; assumption.
  rewrite <- b; right; reflexivity.
  unfold Un_cv in H7; unfold R_dist in H7.
  cut (0 < - f x0).
  intro.
  elim (H7 (- f x0) H8); intros.
  cut (x2 >= x2)%nat; [ intro | unfold ge in |- *; apply le_n ].
  assert (H11 := H9 x2 H10).
  rewrite Rabs_right in H11.
  pattern (- f x0) at 1 in H11; rewrite <- Rplus_0_r in H11.
  unfold Rminus in H11; rewrite (Rplus_comm (f (Wn x2))) in H11.
  assert (H12 := Rplus_lt_reg_r _ _ _ H11).
  assert (H13 := H6 x2).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H13 H12)).
  apply Rle_ge; left; unfold Rminus in |- *; apply Rplus_le_lt_0_compat.
  apply H6.
  exact H8.
  apply Ropp_0_gt_lt_contravar; assumption.
  unfold Wn in |- *; assumption.
  cut (Un_cv Vn x0).
  intros.
  assert (H7 := continuity_seq f Vn x0 (H x0) H5).
  case (total_order_T 0 (f x0)); intro.
  elim s; intro.
  unfold Un_cv in H7; unfold R_dist in H7.
  elim (H7 (f x0) a); intros.
  cut (x2 >= x2)%nat; [ intro | unfold ge in |- *; apply le_n ].
  assert (H10 := H8 x2 H9).
  rewrite Rabs_left in H10.
  pattern (f x0) at 2 in H10; rewrite <- Rplus_0_r in H10.
  rewrite Ropp_minus_distr' in H10.
  unfold Rminus in H10.
  assert (H11 := Rplus_lt_reg_r _ _ _ H10).
  assert (H12 := H6 x2).
  cut (0 < f (Vn x2)).
  intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H13 H12)).
  rewrite <- (Ropp_involutive (f (Vn x2))).
  apply Ropp_0_gt_lt_contravar; assumption.
  apply Rplus_lt_reg_r with (f x0 - f (Vn x2)).
  rewrite Rplus_0_r; replace (f x0 - f (Vn x2) + (f (Vn x2) - f x0)) with 0;
    [ unfold Rminus in |- *; apply Rplus_lt_le_0_compat | ring ].
  assumption.
  apply Ropp_0_ge_le_contravar; apply Rle_ge; apply H6.
  right; rewrite <- b; reflexivity.
  left; assumption.
  unfold Vn in |- *; assumption.
Qed.

Lemma IVT_cor :
  forall (f:R -> R) (x y:R),
    continuity f ->
    x <= y -> f x * f y <= 0 -> { z:R | x <= z <= y /\ f z = 0 }.
Proof.
  intros.
  case (total_order_T 0 (f x)); intro.
  case (total_order_T 0 (f y)); intro.
  elim s; intro.
  elim s0; intro.
  cut (0 < f x * f y);
    [ intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H1 H2))
      | apply Rmult_lt_0_compat; assumption ].
  exists y.
  split.
  split; [ assumption | right; reflexivity ].
  symmetry  in |- *; exact b.
  exists x.
  split.
  split; [ right; reflexivity | assumption ].
  symmetry  in |- *; exact b.
  elim s; intro.
  cut (x < y).
  intro.
  assert (H3 := IVT (- f)%F x y (continuity_opp f H) H2).
  cut ((- f)%F x < 0).
  cut (0 < (- f)%F y).
  intros.
  elim (H3 H5 H4); intros.
  exists x0.
  elim p; intros.
  split.
  assumption.
  unfold opp_fct in H7.
  rewrite <- (Ropp_involutive (f x0)).
  apply Ropp_eq_0_compat; assumption.
  unfold opp_fct in |- *; apply Ropp_0_gt_lt_contravar; assumption.
  unfold opp_fct in |- *.
  apply Rplus_lt_reg_r with (f x); rewrite Rplus_opp_r; rewrite Rplus_0_r;
    assumption.
  inversion H0.
  assumption.
  rewrite H2 in a.
  elim (Rlt_irrefl _ (Rlt_trans _ _ _ r a)).
  exists x.
  split.
  split; [ right; reflexivity | assumption ].
  symmetry  in |- *; assumption.
  case (total_order_T 0 (f y)); intro.
  elim s; intro.
  cut (x < y).
  intro.
  apply IVT; assumption.
  inversion H0.
  assumption.
  rewrite H2 in r.
  elim (Rlt_irrefl _ (Rlt_trans _ _ _ r a)).
  exists y.
  split.
  split; [ assumption | right; reflexivity ].
  symmetry  in |- *; assumption.
  cut (0 < f x * f y).
  intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H2 H1)).
  rewrite <- Rmult_opp_opp; apply Rmult_lt_0_compat;
    apply Ropp_0_gt_lt_contravar; assumption.
Qed.

(** We can now define the square root function as the reciprocal
   transformation of the square root function *)
Lemma Rsqrt_exists :
  forall y:R, 0 <= y -> { z:R | 0 <= z /\ y = Rsqr z }.
Proof.
  intros.
  set (f := fun x:R => Rsqr x - y).
  cut (f 0 <= 0).
  intro.
  cut (continuity f).
  intro.
  case (total_order_T y 1); intro.
  elim s; intro.
  cut (0 <= f 1).
  intro.
  cut (f 0 * f 1 <= 0).
  intro.
  assert (X := IVT_cor f 0 1 H1 (Rlt_le _ _ Rlt_0_1) H3).
  elim X; intros t H4.
  exists t.
  elim H4; intros.
  split.
  elim H5; intros; assumption.
  unfold f in H6.
  apply Rminus_diag_uniq_sym; exact H6.
  rewrite Rmult_comm; pattern 0 at 2 in |- *; rewrite <- (Rmult_0_r (f 1)).
  apply Rmult_le_compat_l; assumption.
  unfold f in |- *.
  rewrite Rsqr_1.
  apply Rplus_le_reg_l with y.
  rewrite Rplus_0_r; rewrite Rplus_comm; unfold Rminus in |- *;
    rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
      left; assumption.
  exists 1.
  split.
  left; apply Rlt_0_1.
  rewrite b; symmetry  in |- *; apply Rsqr_1.
  cut (0 <= f y).
  intro.
  cut (f 0 * f y <= 0).
  intro.
  assert (X := IVT_cor f 0 y H1 H H3).
  elim X; intros t H4.
  exists t.
  elim H4; intros.
  split.
  elim H5; intros; assumption.
  unfold f in H6.
  apply Rminus_diag_uniq_sym; exact H6.
  rewrite Rmult_comm; pattern 0 at 2 in |- *; rewrite <- (Rmult_0_r (f y)).
  apply Rmult_le_compat_l; assumption.
  unfold f in |- *.
  apply Rplus_le_reg_l with y.
  rewrite Rplus_0_r; rewrite Rplus_comm; unfold Rminus in |- *;
    rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
  pattern y at 1 in |- *; rewrite <- Rmult_1_r.
  unfold Rsqr in |- *; apply Rmult_le_compat_l.
  assumption.
  left; exact r.
  replace f with (Rsqr - fct_cte y)%F.
  apply continuity_minus.
  apply derivable_continuous; apply derivable_Rsqr.
  apply derivable_continuous; apply derivable_const.
  reflexivity.
  unfold f in |- *; rewrite Rsqr_0.
  unfold Rminus in |- *; rewrite Rplus_0_l.
  apply Rge_le.
  apply Ropp_0_le_ge_contravar; assumption.
Qed.

(* Definition of the square root: R+->R *)
Definition Rsqrt (y:nonnegreal) : R :=
  let (a,_) := Rsqrt_exists (nonneg y) (cond_nonneg y) in a.

(**********)
Lemma Rsqrt_positivity : forall x:nonnegreal, 0 <= Rsqrt x.
Proof.
  intro.
  assert (X := Rsqrt_exists (nonneg x) (cond_nonneg x)).
  elim X; intros.
  cut (x0 = Rsqrt x).
  intros.
  elim p; intros.
  rewrite H in H0; assumption.
  unfold Rsqrt in |- *.
  case (Rsqrt_exists x (cond_nonneg x)).
  intros.
  elim p; elim a; intros.
  apply Rsqr_inj.
  assumption.
  assumption.
  rewrite <- H0; rewrite <- H2; reflexivity.
Qed.

(**********)
Lemma Rsqrt_Rsqrt : forall x:nonnegreal, Rsqrt x * Rsqrt x = x.
Proof.
  intros.
  assert (X := Rsqrt_exists (nonneg x) (cond_nonneg x)).
  elim X; intros.
  cut (x0 = Rsqrt x).
  intros.
  rewrite <- H.
  elim p; intros.
  rewrite H1; reflexivity.
  unfold Rsqrt in |- *.
  case (Rsqrt_exists x (cond_nonneg x)).
  intros.
  elim p; elim a; intros.
  apply Rsqr_inj.
  assumption.
  assumption.
  rewrite <- H0; rewrite <- H2; reflexivity.
Qed.
