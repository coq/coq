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
Require Import Ranalysis1.
Require Import Rtopology.
Local Open Scope R_scope.

(* The Mean Value Theorem *)
Theorem MVT :
  forall (f g:R -> R) (a b:R) (pr1:forall c:R, a < c < b -> derivable_pt f c)
    (pr2:forall c:R, a < c < b -> derivable_pt g c),
    a < b ->
    (forall c:R, a <= c <= b -> continuity_pt f c) ->
    (forall c:R, a <= c <= b -> continuity_pt g c) ->
    exists c : R,
      (exists P : a < c < b,
        (g b - g a) * derive_pt f c (pr1 c P) =
        (f b - f a) * derive_pt g c (pr2 c P)).
Proof.
  intros; assert (H2 := Rlt_le _ _ H).
  set (h := fun y:R => (g b - g a) * f y - (f b - f a) * g y).
  cut (forall c:R, a < c < b -> derivable_pt h c).
  intro X; cut (forall c:R, a <= c <= b -> continuity_pt h c).
  intro; assert (H4 := continuity_ab_maj h a b H2 H3).
  assert (H5 := continuity_ab_min h a b H2 H3).
  elim H4; intros Mx H6.
  elim H5; intros mx H7.
  cut (h a = h b).
  intro; set (M := h Mx); set (m := h mx).
  cut
    (forall (c:R) (P:a < c < b),
      derive_pt h c (X c P) =
      (g b - g a) * derive_pt f c (pr1 c P) -
      (f b - f a) * derive_pt g c (pr2 c P)).
  intro; case (Req_dec (h a) M); intro.
  case (Req_dec (h a) m); intro.
  cut (forall c:R, a <= c <= b -> h c = M).
  intro; cut (a < (a + b) / 2 < b).
(*** h constant ***)
  intro; exists ((a + b) / 2).
  exists H13.
  apply Rminus_diag_uniq; rewrite <- H9; apply deriv_constant2 with a b.
  elim H13; intros; assumption.
  elim H13; intros; assumption.
  intros; rewrite (H12 ((a + b) / 2)).
  apply H12; split; left; assumption.
  elim H13; intros; split; left; assumption.
  split.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; rewrite double; apply Rplus_lt_compat_l; apply H.
  discrR.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; rewrite Rplus_comm; rewrite double;
    apply Rplus_lt_compat_l; apply H.
  discrR.
  intros; elim H6; intros H13 _.
  elim H7; intros H14 _.
  apply Rle_antisym.
  apply H13; apply H12.
  rewrite H10 in H11; rewrite H11; apply H14; apply H12.
  cut (a < mx < b).
(*** h admet un minimum global sur [a,b] ***)
  intro; exists mx.
  exists H12.
  apply Rminus_diag_uniq; rewrite <- H9; apply deriv_minimum with a b.
  elim H12; intros; assumption.
  elim H12; intros; assumption.
  intros; elim H7; intros.
  apply H15; split; left; assumption.
  elim H7; intros _ H12; elim H12; intros; split.
  inversion H13.
  apply H15.
  rewrite H15 in H11; elim H11; reflexivity.
  inversion H14.
  apply H15.
  rewrite H8 in H11; rewrite <- H15 in H11; elim H11; reflexivity.
  cut (a < Mx < b).
(*** h admet un maximum global sur [a,b] ***)
  intro; exists Mx.
  exists H11.
  apply Rminus_diag_uniq; rewrite <- H9; apply deriv_maximum with a b.
  elim H11; intros; assumption.
  elim H11; intros; assumption.
  intros; elim H6; intros; apply H14.
  split; left; assumption.
  elim H6; intros _ H11; elim H11; intros; split.
  inversion H12.
  apply H14.
  rewrite H14 in H10; elim H10; reflexivity.
  inversion H13.
  apply H14.
  rewrite H8 in H10; rewrite <- H14 in H10; elim H10; reflexivity.
  intros; unfold h;
    replace
    (derive_pt (fun y:R => (g b - g a) * f y - (f b - f a) * g y) c (X c P))
    with
      (derive_pt ((fct_cte (g b - g a) * f)%F - (fct_cte (f b - f a) * g)%F) c
        (derivable_pt_minus _ _ _
          (derivable_pt_mult _ _ _ (derivable_pt_const (g b - g a) c) (pr1 c P))
          (derivable_pt_mult _ _ _ (derivable_pt_const (f b - f a) c) (pr2 c P))));
      [ idtac | apply pr_nu ].
  rewrite derive_pt_minus; do 2 rewrite derive_pt_mult;
    do 2 rewrite derive_pt_const; do 2 rewrite Rmult_0_l;
      do 2 rewrite Rplus_0_l; reflexivity.
  unfold h; ring.
  intros; unfold h;
    change
      (continuity_pt ((fct_cte (g b - g a) * f)%F - (fct_cte (f b - f a) * g)%F)
        c).
  apply continuity_pt_minus; apply continuity_pt_mult.
  apply derivable_continuous_pt; apply derivable_const.
  apply H0; apply H3.
  apply derivable_continuous_pt; apply derivable_const.
  apply H1; apply H3.
  intros;
    change
      (derivable_pt ((fct_cte (g b - g a) * f)%F - (fct_cte (f b - f a) * g)%F)
        c).
  apply derivable_pt_minus; apply derivable_pt_mult.
  apply derivable_pt_const.
  apply (pr1 _ H3).
  apply derivable_pt_const.
  apply (pr2 _ H3).
Qed.

(* Corollaries ... *)
Lemma MVT_cor1 :
  forall (f:R -> R) (a b:R) (pr:derivable f),
    a < b ->
    exists c : R, f b - f a = derive_pt f c (pr c) * (b - a) /\ a < c < b.
Proof.
  intros f a b pr H; cut (forall c:R, a < c < b -> derivable_pt f c);
    [ intro X | intros; apply pr ].
  cut (forall c:R, a < c < b -> derivable_pt id c);
    [ intro X0 | intros; apply derivable_pt_id ].
  cut (forall c:R, a <= c <= b -> continuity_pt f c);
    [ intro | intros; apply derivable_continuous_pt; apply pr ].
  cut (forall c:R, a <= c <= b -> continuity_pt id c);
    [ intro | intros; apply derivable_continuous_pt; apply derivable_id ].
  assert (H2 := MVT f id a b X X0 H H0 H1).
  destruct H2 as (c & P & H4).
  exists c; split.
  cut (derive_pt id c (X0 c P) = derive_pt id c (derivable_pt_id c));
    [ intro H5 | apply pr_nu ].
  rewrite H5 in H4; rewrite (derive_pt_id c) in H4; rewrite Rmult_1_r in H4;
    rewrite <- H4; replace (derive_pt f c (X c P)) with (derive_pt f c (pr c));
      [ idtac | apply pr_nu ]; apply Rmult_comm.
  apply P.
Qed.

Theorem MVT_cor2 :
  forall (f f':R -> R) (a b:R),
    a < b ->
    (forall c:R, a <= c <= b -> derivable_pt_lim f c (f' c)) ->
    exists c : R, f b - f a = f' c * (b - a) /\ a < c < b.
Proof.
  intros f f' a b H H0; cut (forall c:R, a <= c <= b -> derivable_pt f c).
  intro X; cut (forall c:R, a < c < b -> derivable_pt f c).
  intro X0; cut (forall c:R, a <= c <= b -> continuity_pt f c).
  intro; cut (forall c:R, a <= c <= b -> derivable_pt id c).
  intro X1; cut (forall c:R, a < c < b -> derivable_pt id c).
  intro X2; cut (forall c:R, a <= c <= b -> continuity_pt id c).
  intro; elim (MVT f id a b X0 X2 H H1 H2); intros x (P,H3).
  exists x; split.
  cut (derive_pt id x (X2 x P) = 1).
  cut (derive_pt f x (X0 x P) = f' x).
  intros; rewrite H4 in H3; rewrite H5 in H3; unfold id in H3;
    rewrite Rmult_1_r in H3; rewrite Rmult_comm; symmetry ;
      assumption.
  apply derive_pt_eq_0; apply H0; elim P; intros; split; left; assumption.
  apply derive_pt_eq_0; apply derivable_pt_lim_id.
  assumption.
  intros; apply derivable_continuous_pt; apply X1; assumption.
  intros; apply derivable_pt_id.
  intros; apply derivable_pt_id.
  intros; apply derivable_continuous_pt; apply X; assumption.
  intros; elim H1; intros; apply X; split; left; assumption.
  intros; unfold derivable_pt; exists (f' c); apply H0;
    apply H1.
Qed.

Lemma MVT_cor3 :
  forall (f f':R -> R) (a b:R),
    a < b ->
    (forall x:R, a <= x -> x <= b -> derivable_pt_lim f x (f' x)) ->
    exists c : R, a <= c /\ c <= b /\ f b = f a + f' c * (b - a).
Proof.
  intros f f' a b H H0;
    assert (H1 :  exists c : R, f b - f a = f' c * (b - a) /\ a < c < b);
      [ apply MVT_cor2; [ apply H | intros; elim H1; intros; apply (H0 _ H2 H3) ]
        | elim H1; intros; exists x; elim H2; intros; elim H4; intros; split;
          [ left; assumption | split; [ left; assumption | rewrite <- H3; ring ] ] ].
Qed.

Lemma Rolle :
  forall (f:R -> R) (a b:R) (pr:forall x:R, a < x < b -> derivable_pt f x),
    (forall x:R, a <= x <= b -> continuity_pt f x) ->
    a < b ->
    f a = f b ->
    exists c : R, (exists P : a < c < b, derive_pt f c (pr c P) = 0).
Proof.
  intros; assert (H2 : forall x:R, a < x < b -> derivable_pt id x).
  intros; apply derivable_pt_id.
  assert (H3 := MVT f id a b pr H2 H0 H);
    assert (H4 : forall x:R, a <= x <= b -> continuity_pt id x).
  intros; apply derivable_continuous; apply derivable_id.
  destruct (H3 H4) as (c & P & H6). exists c; exists P; rewrite H1 in H6.
  unfold id in H6; unfold Rminus in H6; rewrite Rplus_opp_r in H6.
  rewrite Rmult_0_l in H6; apply Rmult_eq_reg_l with (b - a);
    [ rewrite Rmult_0_r; apply H6
      | apply Rminus_eq_contra; red; intro H7; rewrite H7 in H0;
        elim (Rlt_irrefl _ H0) ].
Qed.

(**********)
Lemma nonneg_derivative_1 :
  forall (f:R -> R) (pr:derivable f),
    (forall x:R, 0 <= derive_pt f x (pr x)) -> increasing f.
Proof.
  intros.
  unfold increasing.
  intros.
  destruct (total_order_T x y) as [[H1| ->]|H1].
  apply Rplus_le_reg_l with (- f x).
  rewrite Rplus_opp_l; rewrite Rplus_comm.
  pose proof (MVT_cor1 f _ _ pr H1) as (c & H3 & H4).
  unfold Rminus in H3.
  rewrite H3.
  apply Rmult_le_pos.
  apply H.
  apply Rplus_le_reg_l with x.
  rewrite Rplus_0_r; replace (x + (y + - x)) with y; [ assumption | ring ].
  right; reflexivity.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H0 H1)).
Qed.

(**********)
Lemma nonpos_derivative_0 :
  forall (f:R -> R) (pr:derivable f),
    decreasing f -> forall x:R, derive_pt f x (pr x) <= 0.
Proof.
  intros f pr H x; assert (H0 := H); unfold decreasing in H0;
    generalize (derivable_derive f x (pr x)); intro; elim H1;
      intros l H2.
  rewrite H2; case (Rtotal_order l 0); intro.
  left; assumption.
  elim H3; intro.
  right; assumption.
  generalize (derive_pt_eq_1 f x l (pr x) H2); intros; cut (0 < l / 2).
  intro; elim (H5 (l / 2) H6); intros delta H7;
    cut (delta / 2 <> 0 /\ 0 < delta / 2 /\ Rabs (delta / 2) < delta).
  intro; decompose [and] H8; intros; generalize (H7 (delta / 2) H9 H12);
    cut ((f (x + delta / 2) - f x) / (delta / 2) <= 0).
  intro; cut (0 < - ((f (x + delta / 2) - f x) / (delta / 2) - l)).
  intro; unfold Rabs;
    case (Rcase_abs ((f (x + delta / 2) - f x) / (delta / 2) - l)) as [Hlt|Hge].
  intros;
    generalize
      (Rplus_lt_compat_r (- l) (- ((f (x + delta / 2) - f x) / (delta / 2) - l))
        (l / 2) H14); unfold Rminus.
  replace (l / 2 + - l) with (- (l / 2)).
  replace (- ((f (x + delta / 2) + - f x) / (delta / 2) + - l) + - l) with
  (- ((f (x + delta / 2) + - f x) / (delta / 2))).
  intro.
  generalize
    (Ropp_lt_gt_contravar (- ((f (x + delta / 2) + - f x) / (delta / 2)))
      (- (l / 2)) H15).
  repeat rewrite Ropp_involutive.
  intro.
  generalize
    (Rlt_trans 0 (l / 2) ((f (x + delta / 2) - f x) / (delta / 2)) H6 H16);
    intro.
  elim
    (Rlt_irrefl 0
      (Rlt_le_trans 0 ((f (x + delta / 2) - f x) / (delta / 2)) 0 H17 H10)).
  ring.
  pattern l at 3; rewrite double_var.
  ring.
  intros.
  generalize
    (Ropp_ge_le_contravar ((f (x + delta / 2) - f x) / (delta / 2) - l) _ Hge).
  rewrite Ropp_0.
  intro.
  elim
    (Rlt_irrefl 0
      (Rlt_le_trans 0 (- ((f (x + delta / 2) - f x) / (delta / 2) - l)) 0 H13
        H15)).
  replace (- ((f (x + delta / 2) - f x) / (delta / 2) - l)) with
  ((f x - f (x + delta / 2)) / (delta / 2) + l).
  unfold Rminus.
  apply Rplus_le_lt_0_compat.
  unfold Rdiv; apply Rmult_le_pos.
  cut (x <= x + delta * / 2).
  intro; generalize (H0 x (x + delta * / 2) H13); intro;
    generalize
      (Rplus_le_compat_l (- f (x + delta / 2)) (f (x + delta / 2)) (f x) H14);
      rewrite Rplus_opp_l; rewrite Rplus_comm; intro; assumption.
  pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
    left; assumption.
  left; apply Rinv_0_lt_compat; assumption.
  assumption.
  rewrite Ropp_minus_distr.
  unfold Rminus.
  rewrite (Rplus_comm l).
  unfold Rdiv.
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite (Rplus_comm (f x)).
  reflexivity.
  replace ((f (x + delta / 2) - f x) / (delta / 2)) with
  (- ((f x - f (x + delta / 2)) / (delta / 2))).
  rewrite <- Ropp_0.
  apply Ropp_ge_le_contravar.
  apply Rle_ge.
  unfold Rdiv; apply Rmult_le_pos.
  cut (x <= x + delta * / 2).
  intro; generalize (H0 x (x + delta * / 2) H10); intro.
  generalize
    (Rplus_le_compat_l (- f (x + delta / 2)) (f (x + delta / 2)) (f x) H13);
    rewrite Rplus_opp_l; rewrite Rplus_comm; intro; assumption.
  pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
    left; assumption.
  left; apply Rinv_0_lt_compat; assumption.
  unfold Rdiv; rewrite <- Ropp_mult_distr_l_reverse.
  rewrite Ropp_minus_distr.
  reflexivity.
  split.
  unfold Rdiv; apply prod_neq_R0.
  generalize (cond_pos delta); intro; red; intro H9; rewrite H9 in H8;
    elim (Rlt_irrefl 0 H8).
  apply Rinv_neq_0_compat; discrR.
  split.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply (cond_pos delta) | apply Rinv_0_lt_compat; prove_sup0 ].
  rewrite Rabs_right.
  unfold Rdiv; apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; rewrite double; pattern (pos delta) at 1;
    rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l; apply (cond_pos delta).
  discrR.
  apply Rle_ge; unfold Rdiv; left; apply Rmult_lt_0_compat.
  apply (cond_pos delta).
  apply Rinv_0_lt_compat; prove_sup0.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply H4 | apply Rinv_0_lt_compat; prove_sup0 ].
Qed.

(**********)
Lemma increasing_decreasing_opp :
  forall f:R -> R, increasing f -> decreasing (- f)%F.
Proof.
  unfold increasing, decreasing, opp_fct; intros; generalize (H x y H0);
    intro; apply Ropp_ge_le_contravar; apply Rle_ge; assumption.
Qed.

(**********)
Lemma nonpos_derivative_1 :
  forall (f:R -> R) (pr:derivable f),
    (forall x:R, derive_pt f x (pr x) <= 0) -> decreasing f.
Proof.
  intros.
  cut (forall h:R, - - f h = f h).
  intro.
  generalize (increasing_decreasing_opp (- f)%F).
  unfold decreasing.
  unfold opp_fct.
  intros.
  rewrite <- (H0 x); rewrite <- (H0 y).
  apply H1.
  cut (forall x:R, 0 <= derive_pt (- f) x (derivable_opp f pr x)).
  intros.
  replace (fun x:R => - f x) with (- f)%F; [ idtac | reflexivity ].
  apply (nonneg_derivative_1 (- f)%F (derivable_opp f pr) H3).
  intro.
  assert (H3 := derive_pt_opp f x0 (pr x0)).
  cut
    (derive_pt (- f) x0 (derivable_pt_opp f x0 (pr x0)) =
      derive_pt (- f) x0 (derivable_opp f pr x0)).
  intro.
  rewrite <- H4.
  rewrite H3.
  rewrite <- Ropp_0; apply Ropp_ge_le_contravar; apply Rle_ge; apply (H x0).
  apply pr_nu.
  assumption.
  intro; ring.
Qed.

(**********)
Lemma positive_derivative :
  forall (f:R -> R) (pr:derivable f),
    (forall x:R, 0 < derive_pt f x (pr x)) -> strict_increasing f.
Proof.
  intros.
  unfold strict_increasing.
  intros.
  apply Rplus_lt_reg_l with (- f x).
  rewrite Rplus_opp_l; rewrite Rplus_comm.
  assert (H1 := MVT_cor1 f _ _ pr H0).
  elim H1; intros.
  elim H2; intros.
  unfold Rminus in H3.
  rewrite H3.
  apply Rmult_lt_0_compat.
  apply H.
  apply Rplus_lt_reg_l with x.
  rewrite Rplus_0_r; replace (x + (y + - x)) with y; [ assumption | ring ].
Qed.

(**********)
Lemma strictincreasing_strictdecreasing_opp :
  forall f:R -> R, strict_increasing f -> strict_decreasing (- f)%F.
Proof.
  unfold strict_increasing, strict_decreasing, opp_fct; intros;
    generalize (H x y H0); intro; apply Ropp_lt_gt_contravar;
      assumption.
Qed.

(**********)
Lemma negative_derivative :
  forall (f:R -> R) (pr:derivable f),
    (forall x:R, derive_pt f x (pr x) < 0) -> strict_decreasing f.
Proof.
  intros.
  cut (forall h:R, - - f h = f h).
  intros.
  generalize (strictincreasing_strictdecreasing_opp (- f)%F).
  unfold strict_decreasing, opp_fct.
  intros.
  rewrite <- (H0 x).
  rewrite <- (H0 y).
  apply H1; [ idtac | assumption ].
  cut (forall x:R, 0 < derive_pt (- f) x (derivable_opp f pr x)).
  intros; eapply positive_derivative; apply H3.
  intro.
  assert (H3 := derive_pt_opp f x0 (pr x0)).
  cut
    (derive_pt (- f) x0 (derivable_pt_opp f x0 (pr x0)) =
      derive_pt (- f) x0 (derivable_opp f pr x0)).
  intro.
  rewrite <- H4; rewrite H3.
  rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; apply (H x0).
  apply pr_nu.
  intro; ring.
Qed.

(**********)
Lemma null_derivative_0 :
  forall (f:R -> R) (pr:derivable f),
    constant f -> forall x:R, derive_pt f x (pr x) = 0.
Proof.
  intros.
  unfold constant in H.
  apply derive_pt_eq_0.
  intros; exists (mkposreal 1 Rlt_0_1); simpl; intros.
  rewrite (H x (x + h)); unfold Rminus; unfold Rdiv;
    rewrite Rplus_opp_r; rewrite Rmult_0_l; rewrite Rplus_opp_r;
      rewrite Rabs_R0; assumption.
Qed.

(**********)
Lemma increasing_decreasing :
  forall f:R -> R, increasing f -> decreasing f -> constant f.
Proof.
  unfold increasing, decreasing, constant; intros;
    case (Rtotal_order x y); intro.
  generalize (Rlt_le x y H1); intro;
    apply (Rle_antisym (f x) (f y) (H x y H2) (H0 x y H2)).
  elim H1; intro.
  rewrite H2; reflexivity.
  generalize (Rlt_le y x H2); intro; symmetry ;
    apply (Rle_antisym (f y) (f x) (H y x H3) (H0 y x H3)).
Qed.

(**********)
Lemma null_derivative_1 :
  forall (f:R -> R) (pr:derivable f),
    (forall x:R, derive_pt f x (pr x) = 0) -> constant f.
Proof.
  intros.
  cut (forall x:R, derive_pt f x (pr x) <= 0).
  cut (forall x:R, 0 <= derive_pt f x (pr x)).
  intros.
  assert (H2 := nonneg_derivative_1 f pr H0).
  assert (H3 := nonpos_derivative_1 f pr H1).
  apply increasing_decreasing; assumption.
  intro; right; symmetry ; apply (H x).
  intro; right; apply (H x).
Qed.

(**********)
Lemma derive_increasing_interv_ax :
  forall (a b:R) (f:R -> R) (pr:derivable f),
    a < b ->
    ((forall t:R, a < t < b -> 0 < derive_pt f t (pr t)) ->
      forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f x < f y) /\
    ((forall t:R, a < t < b -> 0 <= derive_pt f t (pr t)) ->
      forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f x <= f y).
Proof.
  intros.
  split; intros.
  apply Rplus_lt_reg_l with (- f x).
  rewrite Rplus_opp_l; rewrite Rplus_comm.
  assert (H4 := MVT_cor1 f _ _ pr H3).
  elim H4; intros.
  elim H5; intros.
  unfold Rminus in H6.
  rewrite H6.
  apply Rmult_lt_0_compat.
  apply H0.
  elim H7; intros.
  split.
  elim H1; intros.
  apply Rle_lt_trans with x; assumption.
  elim H2; intros.
  apply Rlt_le_trans with y; assumption.
  apply Rplus_lt_reg_l with x.
  rewrite Rplus_0_r; replace (x + (y + - x)) with y; [ assumption | ring ].
  apply Rplus_le_reg_l with (- f x).
  rewrite Rplus_opp_l; rewrite Rplus_comm.
  assert (H4 := MVT_cor1 f _ _ pr H3).
  elim H4; intros.
  elim H5; intros.
  unfold Rminus in H6.
  rewrite H6.
  apply Rmult_le_pos.
  apply H0.
  elim H7; intros.
  split.
  elim H1; intros.
  apply Rle_lt_trans with x; assumption.
  elim H2; intros.
  apply Rlt_le_trans with y; assumption.
  apply Rplus_le_reg_l with x.
  rewrite Rplus_0_r; replace (x + (y + - x)) with y;
    [ left; assumption | ring ].
Qed.

(**********)
Lemma derive_increasing_interv :
  forall (a b:R) (f:R -> R) (pr:derivable f),
    a < b ->
    (forall t:R, a < t < b -> 0 < derive_pt f t (pr t)) ->
    forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f x < f y.
Proof.
  intros.
  generalize (derive_increasing_interv_ax a b f pr H); intro.
  elim H4; intros H5 _; apply (H5 H0 x y H1 H2 H3).
Qed.

(**********)
Lemma derive_increasing_interv_var :
  forall (a b:R) (f:R -> R) (pr:derivable f),
    a < b ->
    (forall t:R, a < t < b -> 0 <= derive_pt f t (pr t)) ->
    forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f x <= f y.
Proof.
  intros a b f pr H H0 x y H1 H2 H3;
    generalize (derive_increasing_interv_ax a b f pr H);
      intro; elim H4; intros _ H5; apply (H5 H0 x y H1 H2 H3).
Qed.

(**********)
(**********)
Theorem IAF :
  forall (f:R -> R) (a b k:R) (pr:derivable f),
    a <= b ->
    (forall c:R, a <= c <= b -> derive_pt f c (pr c) <= k) ->
    f b - f a <= k * (b - a).
Proof.
  intros.
  destruct (total_order_T a b) as [[H1| -> ]|H1].
  pose proof (MVT_cor1 f _ _ pr H1) as (c & -> & H4).
  do 2 rewrite <- (Rmult_comm (b - a)).
  apply Rmult_le_compat_l.
  apply Rplus_le_reg_l with a; rewrite Rplus_0_r.
  replace (a + (b - a)) with b; [ assumption | ring ].
  apply H0.
  elim H4; intros.
  split; left; assumption.
  unfold Rminus; do 2 rewrite Rplus_opp_r.
  rewrite Rmult_0_r; right; reflexivity.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H H1)).
Qed.

Lemma IAF_var :
  forall (f g:R -> R) (a b:R) (pr1:derivable f) (pr2:derivable g),
    a <= b ->
    (forall c:R, a <= c <= b -> derive_pt g c (pr2 c) <= derive_pt f c (pr1 c)) ->
    g b - g a <= f b - f a.
Proof.
  intros.
  cut (derivable (g - f)).
  intro X.
  cut (forall c:R, a <= c <= b -> derive_pt (g - f) c (X c) <= 0).
  intro.
  assert (H2 := IAF (g - f)%F a b 0 X H H1).
  rewrite Rmult_0_l in H2; unfold minus_fct in H2.
  apply Rplus_le_reg_l with (- f b + f a).
  replace (- f b + f a + (f b - f a)) with 0; [ idtac | ring ].
  replace (- f b + f a + (g b - g a)) with (g b - f b - (g a - f a));
  [ apply H2 | ring ].
  intros.
  cut
    (derive_pt (g - f) c (X c) =
      derive_pt (g - f) c (derivable_pt_minus _ _ _ (pr2 c) (pr1 c))).
  intro.
  rewrite H2.
  rewrite derive_pt_minus.
  apply Rplus_le_reg_l with (derive_pt f c (pr1 c)).
  rewrite Rplus_0_r.
  replace
  (derive_pt f c (pr1 c) + (derive_pt g c (pr2 c) - derive_pt f c (pr1 c)))
    with (derive_pt g c (pr2 c)); [ idtac | ring ].
  apply H0; assumption.
  apply pr_nu.
  apply derivable_minus; assumption.
Qed.

(* If f has a null derivative in ]a,b[ and is continue in [a,b], *)
(* then f is constant on [a,b] *)
Lemma null_derivative_loc :
  forall (f:R -> R) (a b:R) (pr:forall x:R, a < x < b -> derivable_pt f x),
    (forall x:R, a <= x <= b -> continuity_pt f x) ->
    (forall (x:R) (P:a < x < b), derive_pt f x (pr x P) = 0) ->
    constant_D_eq f (fun x:R => a <= x <= b) (f a).
Proof.
  intros; unfold constant_D_eq; intros; destruct (total_order_T a b) as [[Hlt|Heq]|Hgt].
  assert (H2 : forall y:R, a < y < x -> derivable_pt id y).
  intros; apply derivable_pt_id.
  assert (H3 : forall y:R, a <= y <= x -> continuity_pt id y).
  intros; apply derivable_continuous; apply derivable_id.
  assert (H4 : forall y:R, a < y < x -> derivable_pt f y).
  intros; apply pr; elim H4; intros; split.
  assumption.
  elim H1; intros; apply Rlt_le_trans with x; assumption.
  assert (H5 : forall y:R, a <= y <= x -> continuity_pt f y).
  intros; apply H; elim H5; intros; split.
  assumption.
  elim H1; intros; apply Rle_trans with x; assumption.
  elim H1; clear H1; intros; elim H1; clear H1; intro.
  assert (H7 := MVT f id a x H4 H2 H1 H5 H3).
  destruct H7 as (c & P & H9).
  assert (H10 : a < c < b).
  split.
  apply P.
  apply Rlt_le_trans with x; [apply P|assumption].
  assert (H11 : derive_pt f c (H4 c P) = 0).
  replace (derive_pt f c (H4 c P)) with (derive_pt f c (pr c H10));
  [ apply H0 | apply pr_nu ].
  assert (H12 : derive_pt id c (H2 c P) = 1).
  apply derive_pt_eq_0; apply derivable_pt_lim_id.
  rewrite H11 in H9; rewrite H12 in H9; rewrite Rmult_0_r in H9;
    rewrite Rmult_1_r in H9; apply Rminus_diag_uniq; symmetry ;
      assumption.
  rewrite H1; reflexivity.
  assert (H2 : x = a).
  rewrite <- Heq in H1; elim H1; intros; apply Rle_antisym; assumption.
  rewrite H2; reflexivity.
  elim H1; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ (Rle_trans _ _ _ H2 H3) Hgt)).
Qed.

(* Unicity of the antiderivative *)
Lemma antiderivative_Ucte :
  forall (f g1 g2:R -> R) (a b:R),
    antiderivative f g1 a b ->
    antiderivative f g2 a b ->
    exists c : R, (forall x:R, a <= x <= b -> g1 x = g2 x + c).
Proof.
  unfold antiderivative; intros; elim H; clear H; intros; elim H0;
    clear H0; intros H0 _; exists (g1 a - g2 a); intros;
      assert (H3 : forall x:R, a <= x <= b -> derivable_pt g1 x).
  intros; unfold derivable_pt; exists (f x0); elim (H x0 H3);
    intros; eapply derive_pt_eq_1; symmetry ;
      apply H4.
  assert (H4 : forall x:R, a <= x <= b -> derivable_pt g2 x).
  intros; unfold derivable_pt; exists (f x0);
    elim (H0 x0 H4); intros; eapply derive_pt_eq_1; symmetry ;
      apply H5.
  assert (H5 : forall x:R, a < x < b -> derivable_pt (g1 - g2) x).
  intros; elim H5; intros; apply derivable_pt_minus;
    [ apply H3; split; left; assumption | apply H4; split; left; assumption ].
  assert (H6 : forall x:R, a <= x <= b -> continuity_pt (g1 - g2) x).
  intros; apply derivable_continuous_pt; apply derivable_pt_minus;
    [ apply H3 | apply H4 ]; assumption.
  assert (H7 : forall (x:R) (P:a < x < b), derive_pt (g1 - g2) x (H5 x P) = 0).
  intros; elim P; intros; apply derive_pt_eq_0; replace 0 with (f x0 - f x0);
    [ idtac | ring ].
  assert (H9 : a <= x0 <= b).
  split; left; assumption.
  apply derivable_pt_lim_minus; [ elim (H _ H9) | elim (H0 _ H9) ]; intros;
    eapply derive_pt_eq_1; symmetry ; apply H10.
  assert (H8 := null_derivative_loc (g1 - g2)%F a b H5 H6 H7);
    unfold constant_D_eq in H8; assert (H9 := H8 _ H2);
      unfold minus_fct in H9; rewrite <- H9; ring.
Qed.

(* A variant of MVT using absolute values. *)
Lemma MVT_abs : 
  forall (f f' : R -> R) (a b : R),
  (forall c : R, Rmin a b <= c <= Rmax a b ->
      derivable_pt_lim f c (f' c)) ->
  exists c : R, Rabs (f b - f a) = Rabs (f' c) * Rabs (b - a) /\
             Rmin a b <= c <= Rmax a b.
Proof.
intros f f' a b.
destruct (Rle_dec a b) as [aleb | blta].
 destruct (Req_dec a b) as [ab | anb].
  unfold Rminus; intros _; exists a; split.
   now rewrite <- ab, !Rplus_opp_r, Rabs_R0, Rmult_0_r.
  split;[apply Rmin_l | apply Rmax_l].
 rewrite Rmax_right, Rmin_left; auto; intros derv.
 destruct (MVT_cor2 f f' a b) as [c [hc intc]];
  [destruct aleb;[assumption | contradiction] | apply derv | ].
 exists c; rewrite hc, Rabs_mult;split;
  [reflexivity | unfold Rle; tauto].
assert (b < a) by (apply Rnot_le_gt; assumption).
assert (b <= a) by (apply Rlt_le; assumption).
rewrite Rmax_left, Rmin_right; try assumption; intros derv.
destruct (MVT_cor2 f f' b a) as [c [hc intc]];
 [assumption | apply derv | ].
exists c; rewrite <- Rabs_Ropp, Ropp_minus_distr, hc, Rabs_mult.
split;[now rewrite <- (Rabs_Ropp (b - a)), Ropp_minus_distr| unfold Rle; tauto].
Qed.

