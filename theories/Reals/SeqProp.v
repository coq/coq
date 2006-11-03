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
Require Import Classical.
Require Import Max.
Open Local Scope R_scope.

Definition Un_decreasing (Un:nat -> R) : Prop :=
  forall n:nat, Un (S n) <= Un n.
Definition opp_seq (Un:nat -> R) (n:nat) : R := - Un n.
Definition has_ub (Un:nat -> R) : Prop := bound (EUn Un).
Definition has_lb (Un:nat -> R) : Prop := bound (EUn (opp_seq Un)).

(**********)
Lemma growing_cv :
  forall Un:nat -> R,
    Un_growing Un -> has_ub Un -> sigT (fun l:R => Un_cv Un l).
Proof.
  unfold Un_growing, Un_cv in |- *; intros;
    destruct (completeness (EUn Un) H0 (EUn_noempty Un)) as [x [H2 H3]].
  exists x; intros eps H1.
  unfold is_upper_bound in H2, H3.
  assert (H5 : forall n:nat, Un n <= x).
  intro n; apply (H2 (Un n) (Un_in_EUn Un n)).
  cut (exists N : nat, x - eps < Un N).
  intro H6; destruct H6 as [N H6]; exists N.
  intros n H7; unfold R_dist in |- *; apply (Rabs_def1 (Un n - x) eps).
  unfold Rgt in H1.
  apply (Rle_lt_trans (Un n - x) 0 eps (Rle_minus (Un n) x (H5 n)) H1).
  fold Un_growing in H; generalize (growing_prop Un n N H H7); intro H8.
  generalize
    (Rlt_le_trans (x - eps) (Un N) (Un n) H6 (Rge_le (Un n) (Un N) H8));
    intro H9; generalize (Rplus_lt_compat_l (- x) (x - eps) (Un n) H9);
      unfold Rminus in |- *; rewrite <- (Rplus_assoc (- x) x (- eps));
        rewrite (Rplus_comm (- x) (Un n)); fold (Un n - x) in |- *;
          rewrite Rplus_opp_l; rewrite (let (H1, H2) := Rplus_ne (- eps) in H2);
            trivial.
  cut (~ (forall N:nat, Un N <= x - eps)).
  intro H6; apply (not_all_not_ex nat (fun N:nat => x - eps < Un N)).
  intro H7; apply H6; intro N; apply Rnot_lt_le; apply H7.
  intro H7; generalize (Un_bound_imp Un (x - eps) H7); intro H8;
    unfold is_upper_bound in H8; generalize (H3 (x - eps) H8);
      apply Rlt_not_le; apply tech_Rgt_minus; exact H1.
Qed.

Lemma decreasing_growing :
  forall Un:nat -> R, Un_decreasing Un -> Un_growing (opp_seq Un).
Proof.
  intro.
  unfold Un_growing, opp_seq, Un_decreasing in |- *.
  intros.
  apply Ropp_le_contravar.
  apply H.
Qed.

Lemma decreasing_cv :
  forall Un:nat -> R,
    Un_decreasing Un -> has_lb Un -> sigT (fun l:R => Un_cv Un l).
Proof.
  intros.
  cut (sigT (fun l:R => Un_cv (opp_seq Un) l) -> sigT (fun l:R => Un_cv Un l)).
  intro X.
  apply X.
  apply growing_cv.
  apply decreasing_growing; assumption.
  exact H0.
  intro X.
  elim X; intros.
  apply existT with (- x).
  unfold Un_cv in p.
  unfold R_dist in p.
  unfold opp_seq in p.
  unfold Un_cv in |- *.
  unfold R_dist in |- *.
  intros.
  elim (p eps H1); intros.
  exists x0; intros.
  assert (H4 := H2 n H3).
  rewrite <- Rabs_Ropp.
  replace (- (Un n - - x)) with (- Un n - x); [ assumption | ring ].
Qed.

(***********)
Lemma maj_sup :
  forall Un:nat -> R, has_ub Un -> sigT (fun l:R => is_lub (EUn Un) l).
Proof.
  intros.
  unfold has_ub in H.
  apply completeness.
  assumption.
  exists (Un 0%nat).
  unfold EUn in |- *.
  exists 0%nat; reflexivity.
Qed.

(**********)
Lemma min_inf :
  forall Un:nat -> R,
    has_lb Un -> sigT (fun l:R => is_lub (EUn (opp_seq Un)) l).
Proof.
  intros; unfold has_lb in H.
  apply completeness.
  assumption.
  exists (- Un 0%nat).
  exists 0%nat.
  reflexivity.
Qed.

Definition majorant (Un:nat -> R) (pr:has_ub Un) : R :=
  match maj_sup Un pr with
    | existT a b => a
  end.

Definition minorant (Un:nat -> R) (pr:has_lb Un) : R :=
  match min_inf Un pr with
    | existT a b => - a
  end.

Lemma maj_ss :
  forall (Un:nat -> R) (k:nat),
    has_ub Un -> has_ub (fun i:nat => Un (k + i)%nat).
Proof.
  intros.
  unfold has_ub in H.
  unfold bound in H.
  elim H; intros.
  unfold is_upper_bound in H0.
  unfold has_ub in |- *.
  exists x.
  unfold is_upper_bound in |- *.
  intros.
  apply H0.
  elim H1; intros.
  exists (k + x1)%nat; assumption.
Qed.

Lemma min_ss :
  forall (Un:nat -> R) (k:nat),
    has_lb Un -> has_lb (fun i:nat => Un (k + i)%nat).
Proof.
  intros.
  unfold has_lb in H.
  unfold bound in H.
  elim H; intros.
  unfold is_upper_bound in H0.
  unfold has_lb in |- *.
  exists x.
  unfold is_upper_bound in |- *.
  intros.
  apply H0.
  elim H1; intros.
  exists (k + x1)%nat; assumption.
Qed.

Definition sequence_majorant (Un:nat -> R) (pr:has_ub Un)
  (i:nat) : R := majorant (fun k:nat => Un (i + k)%nat) (maj_ss Un i pr).

Definition sequence_minorant (Un:nat -> R) (pr:has_lb Un)
  (i:nat) : R := minorant (fun k:nat => Un (i + k)%nat) (min_ss Un i pr).

Lemma Wn_decreasing :
  forall (Un:nat -> R) (pr:has_ub Un), Un_decreasing (sequence_majorant Un pr).
Proof.
  intros.
  unfold Un_decreasing in |- *.
  intro.
  unfold sequence_majorant in |- *.
  assert (H := maj_sup (fun k:nat => Un (S n + k)%nat) (maj_ss Un (S n) pr)).
  assert (H0 := maj_sup (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr)).
  elim H; intros.
  elim H0; intros.
  cut (majorant (fun k:nat => Un (S n + k)%nat) (maj_ss Un (S n) pr) = x);
    [ intro Maj1; rewrite Maj1 | idtac ].
  cut (majorant (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr) = x0);
    [ intro Maj2; rewrite Maj2 | idtac ].
  unfold is_lub in p.
  unfold is_lub in p0.
  elim p; intros.
  apply H2.
  elim p0; intros.
  unfold is_upper_bound in |- *.
  intros.
  unfold is_upper_bound in H3.
  apply H3.
  elim H5; intros.
  exists (1 + x2)%nat.
  replace (n + (1 + x2))%nat with (S n + x2)%nat.
  assumption.
  replace (S n) with (1 + n)%nat; [ ring | ring ].
  cut
    (is_lub (EUn (fun k:nat => Un (n + k)%nat))
      (majorant (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr))).
  intro.
  unfold is_lub in p0; unfold is_lub in H1.
  elim p0; intros; elim H1; intros.
  assert (H6 := H5 x0 H2).
  assert
    (H7 := H3 (majorant (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr)) H4).
  apply Rle_antisym; assumption.
  unfold majorant in |- *.
  case (maj_sup (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr)).
  trivial.
  cut
    (is_lub (EUn (fun k:nat => Un (S n + k)%nat))
      (majorant (fun k:nat => Un (S n + k)%nat) (maj_ss Un (S n) pr))).
  intro.
  unfold is_lub in p; unfold is_lub in H1.
  elim p; intros; elim H1; intros.
  assert (H6 := H5 x H2).
  assert
    (H7 :=
      H3 (majorant (fun k:nat => Un (S n + k)%nat) (maj_ss Un (S n) pr)) H4).
  apply Rle_antisym; assumption.
  unfold majorant in |- *.
  case (maj_sup (fun k:nat => Un (S n + k)%nat) (maj_ss Un (S n) pr)).
  trivial.
Qed.

Lemma Vn_growing :
  forall (Un:nat -> R) (pr:has_lb Un), Un_growing (sequence_minorant Un pr).
Proof.
  intros.
  unfold Un_growing in |- *.
  intro.
  unfold sequence_minorant in |- *.
  assert (H := min_inf (fun k:nat => Un (S n + k)%nat) (min_ss Un (S n) pr)).
  assert (H0 := min_inf (fun k:nat => Un (n + k)%nat) (min_ss Un n pr)).
  elim H; intros.
  elim H0; intros.
  cut (minorant (fun k:nat => Un (S n + k)%nat) (min_ss Un (S n) pr) = - x);
    [ intro Maj1; rewrite Maj1 | idtac ].
  cut (minorant (fun k:nat => Un (n + k)%nat) (min_ss Un n pr) = - x0);
    [ intro Maj2; rewrite Maj2 | idtac ].
  unfold is_lub in p.
  unfold is_lub in p0.
  elim p; intros.
  apply Ropp_le_contravar.
  apply H2.
  elim p0; intros.
  unfold is_upper_bound in |- *.
  intros.
  unfold is_upper_bound in H3.
  apply H3.
  elim H5; intros.
  exists (1 + x2)%nat.
  unfold opp_seq in H6.
  unfold opp_seq in |- *.
  replace (n + (1 + x2))%nat with (S n + x2)%nat.
  assumption.
  replace (S n) with (1 + n)%nat; [ ring | ring ].
  cut
    (is_lub (EUn (opp_seq (fun k:nat => Un (n + k)%nat)))
      (- minorant (fun k:nat => Un (n + k)%nat) (min_ss Un n pr))).
  intro.
  unfold is_lub in p0; unfold is_lub in H1.
  elim p0; intros; elim H1; intros.
  assert (H6 := H5 x0 H2).
  assert
    (H7 := H3 (- minorant (fun k:nat => Un (n + k)%nat) (min_ss Un n pr)) H4).
  rewrite <-
    (Ropp_involutive (minorant (fun k:nat => Un (n + k)%nat) (min_ss Un n pr)))
    .
  apply Ropp_eq_compat; apply Rle_antisym; assumption.
  unfold minorant in |- *.
  case (min_inf (fun k:nat => Un (n + k)%nat) (min_ss Un n pr)).
  intro; rewrite Ropp_involutive.
  trivial.
  cut
    (is_lub (EUn (opp_seq (fun k:nat => Un (S n + k)%nat)))
      (- minorant (fun k:nat => Un (S n + k)%nat) (min_ss Un (S n) pr))).
  intro.
  unfold is_lub in p; unfold is_lub in H1.
  elim p; intros; elim H1; intros.
  assert (H6 := H5 x H2).
  assert
    (H7 :=
      H3 (- minorant (fun k:nat => Un (S n + k)%nat) (min_ss Un (S n) pr)) H4).
  rewrite <-
    (Ropp_involutive
      (minorant (fun k:nat => Un (S n + k)%nat) (min_ss Un (S n) pr)))
    .
  apply Ropp_eq_compat; apply Rle_antisym; assumption.
  unfold minorant in |- *.
  case (min_inf (fun k:nat => Un (S n + k)%nat) (min_ss Un (S n) pr)).
  intro; rewrite Ropp_involutive.
  trivial.
Qed.

(**********)
Lemma Vn_Un_Wn_order :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un)
    (n:nat), sequence_minorant Un pr2 n <= Un n <= sequence_majorant Un pr1 n.
Proof.
  intros.
  split.
  unfold sequence_minorant in |- *.
  cut
    (sigT (fun l:R => is_lub (EUn (opp_seq (fun i:nat => Un (n + i)%nat))) l)).
  intro X.
  elim X; intros.
  replace (minorant (fun k:nat => Un (n + k)%nat) (min_ss Un n pr2)) with (- x).
  unfold is_lub in p.
  elim p; intros.
  unfold is_upper_bound in H.
  rewrite <- (Ropp_involutive (Un n)).
  apply Ropp_le_contravar.
  apply H.
  exists 0%nat.
  unfold opp_seq in |- *.
  replace (n + 0)%nat with n; [ reflexivity | ring ].
  cut
    (is_lub (EUn (opp_seq (fun k:nat => Un (n + k)%nat)))
      (- minorant (fun k:nat => Un (n + k)%nat) (min_ss Un n pr2))).
  intro.
  unfold is_lub in p; unfold is_lub in H.
  elim p; intros; elim H; intros.
  assert (H4 := H3 x H0).
  assert
    (H5 := H1 (- minorant (fun k:nat => Un (n + k)%nat) (min_ss Un n pr2)) H2).
  rewrite <-
    (Ropp_involutive (minorant (fun k:nat => Un (n + k)%nat) (min_ss Un n pr2)))
    .
  apply Ropp_eq_compat; apply Rle_antisym; assumption.
  unfold minorant in |- *.
  case (min_inf (fun k:nat => Un (n + k)%nat) (min_ss Un n pr2)).
  intro; rewrite Ropp_involutive.
  trivial.
  apply min_inf.
  apply min_ss; assumption.
  unfold sequence_majorant in |- *.
  cut (sigT (fun l:R => is_lub (EUn (fun i:nat => Un (n + i)%nat)) l)).
  intro X.
  elim X; intros.
  replace (majorant (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr1)) with x.
  unfold is_lub in p.
  elim p; intros.
  unfold is_upper_bound in H.
  apply H.
  exists 0%nat.
  replace (n + 0)%nat with n; [ reflexivity | ring ].
  cut
    (is_lub (EUn (fun k:nat => Un (n + k)%nat))
      (majorant (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr1))).
  intro.
  unfold is_lub in p; unfold is_lub in H.
  elim p; intros; elim H; intros.
  assert (H4 := H3 x H0).
  assert
    (H5 := H1 (majorant (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr1)) H2).
  apply Rle_antisym; assumption.
  unfold majorant in |- *.
  case (maj_sup (fun k:nat => Un (n + k)%nat) (maj_ss Un n pr1)).
  intro; trivial.
  apply maj_sup.
  apply maj_ss; assumption.
Qed.

Lemma min_maj :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un),
    has_ub (sequence_minorant Un pr2).
Proof.
  intros.
  assert (H := Vn_Un_Wn_order Un pr1 pr2).
  unfold has_ub in |- *.
  unfold bound in |- *.
  unfold has_ub in pr1.
  unfold bound in pr1.
  elim pr1; intros.
  exists x.
  unfold is_upper_bound in |- *.
  intros.
  unfold is_upper_bound in H0.
  elim H1; intros.
  rewrite H2.
  apply Rle_trans with (Un x1).
  assert (H3 := H x1); elim H3; intros; assumption.
  apply H0.
  exists x1; reflexivity.
Qed.

Lemma maj_min :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un),
    has_lb (sequence_majorant Un pr1).
Proof.
  intros.
  assert (H := Vn_Un_Wn_order Un pr1 pr2).
  unfold has_lb in |- *.
  unfold bound in |- *.
  unfold has_lb in pr2.
  unfold bound in pr2.
  elim pr2; intros.
  exists x.
  unfold is_upper_bound in |- *.
  intros.
  unfold is_upper_bound in H0.
  elim H1; intros.
  rewrite H2.
  apply Rle_trans with (opp_seq Un x1).
  assert (H3 := H x1); elim H3; intros.
  unfold opp_seq in |- *; apply Ropp_le_contravar.
  assumption.
  apply H0.
  exists x1; reflexivity.
Qed.

(**********)
Lemma cauchy_maj : forall Un:nat -> R, Cauchy_crit Un -> has_ub Un.
Proof.
  intros.
  unfold has_ub in |- *.
  apply cauchy_bound.
  assumption.
Qed.

(**********)
Lemma cauchy_opp :
  forall Un:nat -> R, Cauchy_crit Un -> Cauchy_crit (opp_seq Un).
Proof.
  intro.
  unfold Cauchy_crit in |- *.
  unfold R_dist in |- *.
  intros.
  elim (H eps H0); intros.
  exists x; intros.
  unfold opp_seq in |- *.
  rewrite <- Rabs_Ropp.
  replace (- (- Un n - - Un m)) with (Un n - Un m);
  [ apply H1; assumption | ring ].
Qed.

(**********)
Lemma cauchy_min : forall Un:nat -> R, Cauchy_crit Un -> has_lb Un.
Proof.
  intros.
  unfold has_lb in |- *.
  assert (H0 := cauchy_opp _ H).
  apply cauchy_bound.
  assumption.
Qed.

(**********)
Lemma maj_cv :
  forall (Un:nat -> R) (pr:Cauchy_crit Un),
    sigT (fun l:R => Un_cv (sequence_majorant Un (cauchy_maj Un pr)) l).
Proof.
  intros.
  apply decreasing_cv.
  apply Wn_decreasing.
  apply maj_min.
  apply cauchy_min.
  assumption.
Qed.

(**********)
Lemma min_cv :
  forall (Un:nat -> R) (pr:Cauchy_crit Un),
    sigT (fun l:R => Un_cv (sequence_minorant Un (cauchy_min Un pr)) l).
Proof.
  intros.
  apply growing_cv.
  apply Vn_growing.
  apply min_maj.
  apply cauchy_maj.
  assumption.
Qed.

Lemma cond_eq :
  forall x y:R, (forall eps:R, 0 < eps -> Rabs (x - y) < eps) -> x = y.
Proof.
  intros.
  case (total_order_T x y); intro.
  elim s; intro.
  cut (0 < y - x).
  intro.
  assert (H1 := H (y - x) H0).
  rewrite <- Rabs_Ropp in H1.
  cut (- (x - y) = y - x); [ intro; rewrite H2 in H1 | ring ].
  rewrite Rabs_right in H1.
  elim (Rlt_irrefl _ H1).
  left; assumption.
  apply Rplus_lt_reg_r with x.
  rewrite Rplus_0_r; replace (x + (y - x)) with y; [ assumption | ring ].
  assumption.
  cut (0 < x - y).
  intro.
  assert (H1 := H (x - y) H0).
  rewrite Rabs_right in H1.
  elim (Rlt_irrefl _ H1).
  left; assumption.
  apply Rplus_lt_reg_r with y.
  rewrite Rplus_0_r; replace (y + (x - y)) with x; [ assumption | ring ].
Qed.

Lemma not_Rlt : forall r1 r2:R, ~ r1 < r2 -> r1 >= r2.
Proof.
  intros r1 r2; generalize (Rtotal_order r1 r2); unfold Rge in |- *.
  tauto.
Qed.

(**********)
Lemma approx_maj :
  forall (Un:nat -> R) (pr:has_ub Un) (eps:R),
    0 < eps ->  exists k : nat, Rabs (majorant Un pr - Un k) < eps.
Proof.
  intros.
  set (P := fun k:nat => Rabs (majorant Un pr - Un k) < eps).
  unfold P in |- *.
  cut
    ((exists k : nat, P k) ->
      exists k : nat, Rabs (majorant Un pr - Un k) < eps).
  intros.
  apply H0.
  apply not_all_not_ex.
  red in |- *; intro.
  2: unfold P in |- *; trivial.
  unfold P in H1.
  cut (forall n:nat, Rabs (majorant Un pr - Un n) >= eps).
  intro.
  cut (is_lub (EUn Un) (majorant Un pr)).
  intro.
  unfold is_lub in H3.
  unfold is_upper_bound in H3.
  elim H3; intros.
  cut (forall n:nat, eps <= majorant Un pr - Un n).
  intro.
  cut (forall n:nat, Un n <= majorant Un pr - eps).
  intro.
  cut (forall x:R, EUn Un x -> x <= majorant Un pr - eps).
  intro.
  assert (H9 := H5 (majorant Un pr - eps) H8).
  cut (eps <= 0).
  intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H H10)).
  apply Rplus_le_reg_l with (majorant Un pr - eps).
  rewrite Rplus_0_r.
  replace (majorant Un pr - eps + eps) with (majorant Un pr);
  [ assumption | ring ].
  intros.
  unfold EUn in H8.
  elim H8; intros.
  rewrite H9; apply H7.
  intro.
  assert (H7 := H6 n).
  apply Rplus_le_reg_l with (eps - Un n).
  replace (eps - Un n + Un n) with eps.
  replace (eps - Un n + (majorant Un pr - eps)) with (majorant Un pr - Un n).
  assumption.
  ring.
  ring.
  intro.
  assert (H6 := H2 n).
  rewrite Rabs_right in H6.
  apply Rge_le.
  assumption.
  apply Rle_ge.
  apply Rplus_le_reg_l with (Un n).
  rewrite Rplus_0_r;
    replace (Un n + (majorant Un pr - Un n)) with (majorant Un pr);
    [ apply H4 | ring ].
  exists n; reflexivity.
  unfold majorant in |- *.
  case (maj_sup Un pr).
  trivial.
  intro.
  assert (H2 := H1 n).
  apply not_Rlt; assumption.
Qed.

(**********)
Lemma approx_min :
  forall (Un:nat -> R) (pr:has_lb Un) (eps:R),
    0 < eps ->  exists k : nat, Rabs (minorant Un pr - Un k) < eps.
Proof.
  intros.
  set (P := fun k:nat => Rabs (minorant Un pr - Un k) < eps).
  unfold P in |- *.
  cut
    ((exists k : nat, P k) ->
      exists k : nat, Rabs (minorant Un pr - Un k) < eps).
  intros.
  apply H0.
  apply not_all_not_ex.
  red in |- *; intro.
  2: unfold P in |- *; trivial.
  unfold P in H1.
  cut (forall n:nat, Rabs (minorant Un pr - Un n) >= eps).
  intro.
  cut (is_lub (EUn (opp_seq Un)) (- minorant Un pr)).
  intro.
  unfold is_lub in H3.
  unfold is_upper_bound in H3.
  elim H3; intros.
  cut (forall n:nat, eps <= Un n - minorant Un pr).
  intro.
  cut (forall n:nat, opp_seq Un n <= - minorant Un pr - eps).
  intro.
  cut (forall x:R, EUn (opp_seq Un) x -> x <= - minorant Un pr - eps).
  intro.
  assert (H9 := H5 (- minorant Un pr - eps) H8).
  cut (eps <= 0).
  intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H H10)).
  apply Rplus_le_reg_l with (- minorant Un pr - eps).
  rewrite Rplus_0_r.
  replace (- minorant Un pr - eps + eps) with (- minorant Un pr);
  [ assumption | ring ].
  intros.
  unfold EUn in H8.
  elim H8; intros.
  rewrite H9; apply H7.
  intro.
  assert (H7 := H6 n).
  unfold opp_seq in |- *.
  apply Rplus_le_reg_l with (eps + Un n).
  replace (eps + Un n + - Un n) with eps.
  replace (eps + Un n + (- minorant Un pr - eps)) with (Un n - minorant Un pr).
  assumption.
  ring.
  ring.
  intro.
  assert (H6 := H2 n).
  rewrite Rabs_left1 in H6.
  apply Rge_le.
  replace (Un n - minorant Un pr) with (- (minorant Un pr - Un n));
  [ assumption | ring ].
  apply Rplus_le_reg_l with (- minorant Un pr).
  rewrite Rplus_0_r;
    replace (- minorant Un pr + (minorant Un pr - Un n)) with (- Un n).
  apply H4.
  exists n; reflexivity.
  ring.
  unfold minorant in |- *.
  case (min_inf Un pr).
  intro.
  rewrite Ropp_involutive.
  trivial.
  intro.
  assert (H2 := H1 n).
  apply not_Rlt; assumption.
Qed.

(** Unicity of limit for convergent sequences *)
Lemma UL_sequence :
  forall (Un:nat -> R) (l1 l2:R), Un_cv Un l1 -> Un_cv Un l2 -> l1 = l2.
Proof.
  intros Un l1 l2; unfold Un_cv in |- *; unfold R_dist in |- *; intros.
  apply cond_eq.
  intros; cut (0 < eps / 2);
    [ intro
      | unfold Rdiv in |- *; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H (eps / 2) H2); intros.
  elim (H0 (eps / 2) H2); intros.
  set (N := max x x0).
  apply Rle_lt_trans with (Rabs (l1 - Un N) + Rabs (Un N - l2)).
  replace (l1 - l2) with (l1 - Un N + (Un N - l2));
  [ apply Rabs_triang | ring ].
  rewrite (double_var eps); apply Rplus_lt_compat.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H3;
    unfold ge, N in |- *; apply le_max_l.
  apply H4; unfold ge, N in |- *; apply le_max_r.
Qed.

(**********)
Lemma CV_plus :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i + Bn i) (l1 + l2).
Proof.
  unfold Un_cv in |- *; unfold R_dist in |- *; intros.
  cut (0 < eps / 2);
    [ intro
      | unfold Rdiv in |- *; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H (eps / 2) H2); intros.
  elim (H0 (eps / 2) H2); intros.
  set (N := max x x0).
  exists N; intros.
  replace (An n + Bn n - (l1 + l2)) with (An n - l1 + (Bn n - l2));
  [ idtac | ring ].
  apply Rle_lt_trans with (Rabs (An n - l1) + Rabs (Bn n - l2)).
  apply Rabs_triang.
  rewrite (double_var eps); apply Rplus_lt_compat.
  apply H3; unfold ge in |- *; apply le_trans with N;
    [ unfold N in |- *; apply le_max_l | assumption ].
  apply H4; unfold ge in |- *; apply le_trans with N;
    [ unfold N in |- *; apply le_max_r | assumption ].
Qed.

(**********)
Lemma cv_cvabs :
  forall (Un:nat -> R) (l:R),
    Un_cv Un l -> Un_cv (fun i:nat => Rabs (Un i)) (Rabs l).
Proof.
  unfold Un_cv in |- *; unfold R_dist in |- *; intros.
  elim (H eps H0); intros.
  exists x; intros.
  apply Rle_lt_trans with (Rabs (Un n - l)).
  apply Rabs_triang_inv2.
  apply H1; assumption.
Qed.

(**********)
Lemma CV_Cauchy :
  forall Un:nat -> R, sigT (fun l:R => Un_cv Un l) -> Cauchy_crit Un.
Proof.
  intros Un X; elim X; intros.
  unfold Cauchy_crit in |- *; intros.
  unfold Un_cv in p; unfold R_dist in p.
  cut (0 < eps / 2);
    [ intro
      | unfold Rdiv in |- *; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (p (eps / 2) H0); intros.
  exists x0; intros.
  unfold R_dist in |- *;
    apply Rle_lt_trans with (Rabs (Un n - x) + Rabs (x - Un m)).
  replace (Un n - Un m) with (Un n - x + (x - Un m));
  [ apply Rabs_triang | ring ].
  rewrite (double_var eps); apply Rplus_lt_compat.
  apply H1; assumption.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H1; assumption.
Qed.

(**********)
Lemma maj_by_pos :
  forall Un:nat -> R,
    sigT (fun l:R => Un_cv Un l) ->
    exists l : R, 0 < l /\ (forall n:nat, Rabs (Un n) <= l).
Proof.
  intros Un X; elim X; intros.
  cut (sigT (fun l:R => Un_cv (fun k:nat => Rabs (Un k)) l)).
  intro X0.
  assert (H := CV_Cauchy (fun k:nat => Rabs (Un k)) X0).
  assert (H0 := cauchy_bound (fun k:nat => Rabs (Un k)) H).
  elim H0; intros.
  exists (x0 + 1).
  cut (0 <= x0).
  intro.
  split.
  apply Rplus_le_lt_0_compat; [ assumption | apply Rlt_0_1 ].
  intros.
  apply Rle_trans with x0.
  unfold is_upper_bound in H1.
  apply H1.
  exists n; reflexivity.
  pattern x0 at 1 in |- *; rewrite <- Rplus_0_r; apply Rplus_le_compat_l; left;
    apply Rlt_0_1.
  apply Rle_trans with (Rabs (Un 0%nat)).
  apply Rabs_pos.
  unfold is_upper_bound in H1.
  apply H1.
  exists 0%nat; reflexivity.
  apply existT with (Rabs x).
  apply cv_cvabs; assumption.
Qed.

(**********)
Lemma CV_mult :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i * Bn i) (l1 * l2).
Proof.
  intros.
  cut (sigT (fun l:R => Un_cv An l)).
  intro X.
  assert (H1 := maj_by_pos An X).
  elim H1; intros M H2.
  elim H2; intros.
  unfold Un_cv in |- *; unfold R_dist in |- *; intros.
  cut (0 < eps / (2 * M)).
  intro.
  case (Req_dec l2 0); intro.
  unfold Un_cv in H0; unfold R_dist in H0.
  elim (H0 (eps / (2 * M)) H6); intros.
  exists x; intros.
  apply Rle_lt_trans with
    (Rabs (An n * Bn n - An n * l2) + Rabs (An n * l2 - l1 * l2)).
  replace (An n * Bn n - l1 * l2) with
  (An n * Bn n - An n * l2 + (An n * l2 - l1 * l2));
  [ apply Rabs_triang | ring ].
  replace (Rabs (An n * Bn n - An n * l2)) with
  (Rabs (An n) * Rabs (Bn n - l2)).
  replace (Rabs (An n * l2 - l1 * l2)) with 0.
  rewrite Rplus_0_r.
  apply Rle_lt_trans with (M * Rabs (Bn n - l2)).
  do 2 rewrite <- (Rmult_comm (Rabs (Bn n - l2))).
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply H4.
  apply Rmult_lt_reg_l with (/ M).
  apply Rinv_0_lt_compat; apply H3.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; rewrite (Rmult_comm (/ M)).
  apply Rlt_trans with (eps / (2 * M)).
  apply H8; assumption.
  unfold Rdiv in |- *; rewrite Rinv_mult_distr.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  replace (2 * (eps * (/ 2 * / M))) with (2 * / 2 * (eps * / M));
  [ idtac | ring ].
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; rewrite double.
  pattern (eps * / M) at 1 in |- *; rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; assumption ].
  discrR.
  discrR.
  red in |- *; intro; rewrite H10 in H3; elim (Rlt_irrefl _ H3).
  red in |- *; intro; rewrite H10 in H3; elim (Rlt_irrefl _ H3).
  rewrite H7; do 2 rewrite Rmult_0_r; unfold Rminus in |- *;
    rewrite Rplus_opp_r; rewrite Rabs_R0; reflexivity.
  replace (An n * Bn n - An n * l2) with (An n * (Bn n - l2)); [ idtac | ring ].
  symmetry  in |- *; apply Rabs_mult.
  cut (0 < eps / (2 * Rabs l2)).
  intro.
  unfold Un_cv in H; unfold R_dist in H; unfold Un_cv in H0;
    unfold R_dist in H0.
  elim (H (eps / (2 * Rabs l2)) H8); intros N1 H9.
  elim (H0 (eps / (2 * M)) H6); intros N2 H10.
  set (N := max N1 N2).
  exists N; intros.
  apply Rle_lt_trans with
    (Rabs (An n * Bn n - An n * l2) + Rabs (An n * l2 - l1 * l2)).
  replace (An n * Bn n - l1 * l2) with
  (An n * Bn n - An n * l2 + (An n * l2 - l1 * l2));
  [ apply Rabs_triang | ring ].
  replace (Rabs (An n * Bn n - An n * l2)) with
  (Rabs (An n) * Rabs (Bn n - l2)).
  replace (Rabs (An n * l2 - l1 * l2)) with (Rabs l2 * Rabs (An n - l1)).
  rewrite (double_var eps); apply Rplus_lt_compat.
  apply Rle_lt_trans with (M * Rabs (Bn n - l2)).
  do 2 rewrite <- (Rmult_comm (Rabs (Bn n - l2))).
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply H4.
  apply Rmult_lt_reg_l with (/ M).
  apply Rinv_0_lt_compat; apply H3.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; rewrite (Rmult_comm (/ M)).
  apply Rlt_le_trans with (eps / (2 * M)).
  apply H10.
  unfold ge in |- *; apply le_trans with N.
  unfold N in |- *; apply le_max_r.
  assumption.
  unfold Rdiv in |- *; rewrite Rinv_mult_distr.
  right; ring.
  discrR.
  red in |- *; intro; rewrite H12 in H3; elim (Rlt_irrefl _ H3).
  red in |- *; intro; rewrite H12 in H3; elim (Rlt_irrefl _ H3).
  apply Rmult_lt_reg_l with (/ Rabs l2).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; apply Rlt_le_trans with (eps / (2 * Rabs l2)).
  apply H9.
  unfold ge in |- *; apply le_trans with N.
  unfold N in |- *; apply le_max_l.
  assumption.
  unfold Rdiv in |- *; right; rewrite Rinv_mult_distr.
  ring.
  discrR.
  apply Rabs_no_R0; assumption.
  apply Rabs_no_R0; assumption.
  replace (An n * l2 - l1 * l2) with (l2 * (An n - l1));
  [ symmetry  in |- *; apply Rabs_mult | ring ].
  replace (An n * Bn n - An n * l2) with (An n * (Bn n - l2));
  [ symmetry  in |- *; apply Rabs_mult | ring ].
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
    [ prove_sup0 | apply Rabs_pos_lt; assumption ].
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ assumption
      | apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
        [ prove_sup0 | assumption ] ].
  apply existT with l1; assumption.
Qed.

Lemma tech9 :
  forall Un:nat -> R,
    Un_growing Un -> forall m n:nat, (m <= n)%nat -> Un m <= Un n.
Proof.
  intros; unfold Un_growing in H.
  induction  n as [| n Hrecn].
  induction  m as [| m Hrecm].
  right; reflexivity.
  elim (le_Sn_O _ H0).
  cut ((m <= n)%nat \/ m = S n).
  intro; elim H1; intro.
  apply Rle_trans with (Un n).
  apply Hrecn; assumption.
  apply H.
  rewrite H2; right; reflexivity.
  inversion H0.
  right; reflexivity.
  left; assumption.
Qed.

Lemma tech10 :
  forall (Un:nat -> R) (x:R), Un_growing Un -> is_lub (EUn Un) x -> Un_cv Un x.
Proof.
  intros; cut (bound (EUn Un)).
  intro; assert (H2 := Un_cv_crit _ H H1).
  elim H2; intros.
  case (total_order_T x x0); intro.
  elim s; intro.
  cut (forall n:nat, Un n <= x).
  intro; unfold Un_cv in H3; cut (0 < x0 - x).
  intro; elim (H3 (x0 - x) H5); intros.
  cut (x1 >= x1)%nat.
  intro; assert (H8 := H6 x1 H7).
  unfold R_dist in H8; rewrite Rabs_left1 in H8.
  rewrite Ropp_minus_distr in H8; unfold Rminus in H8.
  assert (H9 := Rplus_lt_reg_r x0 _ _ H8).
  assert (H10 := Ropp_lt_cancel _ _ H9).
  assert (H11 := H4 x1).
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H10 H11)).
  apply Rle_minus; apply Rle_trans with x.
  apply H4.
  left; assumption.
  unfold ge in |- *; apply le_n.
  apply Rgt_minus; assumption.
  intro; unfold is_lub in H0; unfold is_upper_bound in H0; elim H0; intros.
  apply H4; unfold EUn in |- *; exists n; reflexivity.
  rewrite b; assumption.
  cut (forall n:nat, Un n <= x0).
  intro; unfold is_lub in H0; unfold is_upper_bound in H0; elim H0; intros.
  cut (forall y:R, EUn Un y -> y <= x0).
  intro; assert (H8 := H6 _ H7).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H8 r)).
  unfold EUn in |- *; intros; elim H7; intros.
  rewrite H8; apply H4.
  intro; case (Rle_dec (Un n) x0); intro.
  assumption.
  cut (forall n0:nat, (n <= n0)%nat -> x0 < Un n0).
  intro; unfold Un_cv in H3; cut (0 < Un n - x0).
  intro; elim (H3 (Un n - x0) H5); intros.
  cut (max n x1 >= x1)%nat.
  intro; assert (H8 := H6 (max n x1) H7).
  unfold R_dist in H8.
  rewrite Rabs_right in H8.
  unfold Rminus in H8; do 2 rewrite <- (Rplus_comm (- x0)) in H8.
  assert (H9 := Rplus_lt_reg_r _ _ _ H8).
  cut (Un n <= Un (max n x1)).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H10 H9)).
  apply tech9; [ assumption | apply le_max_l ].
  apply Rge_trans with (Un n - x0).
  unfold Rminus in |- *; apply Rle_ge; do 2 rewrite <- (Rplus_comm (- x0));
    apply Rplus_le_compat_l.
  apply tech9; [ assumption | apply le_max_l ].
  left; assumption.
  unfold ge in |- *; apply le_max_r.
  apply Rplus_lt_reg_r with x0.
  rewrite Rplus_0_r; unfold Rminus in |- *; rewrite (Rplus_comm x0);
    rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
      apply H4; apply le_n.
  intros; apply Rlt_le_trans with (Un n).
  case (Rlt_le_dec x0 (Un n)); intro.
  assumption.
  elim n0; assumption.
  apply tech9; assumption.
  unfold bound in |- *; exists x; unfold is_lub in H0; elim H0; intros;
    assumption.
Qed.

Lemma tech13 :
  forall (An:nat -> R) (k:R),
    0 <= k < 1 ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    exists k0 : R,
      k < k0 < 1 /\
      (exists N : nat,
        (forall n:nat, (N <= n)%nat -> Rabs (An (S n) / An n) < k0)).
Proof.
  intros; exists (k + (1 - k) / 2).
  split.
  split.
  pattern k at 1 in |- *; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  apply Rplus_lt_reg_r with k; rewrite Rplus_0_r; replace (k + (1 - k)) with 1;
    [ elim H; intros; assumption | ring ].
  apply Rinv_0_lt_compat; prove_sup0.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv in |- *; rewrite Rmult_1_r; rewrite Rmult_plus_distr_l;
    pattern 2 at 1 in |- *; rewrite Rmult_comm; rewrite Rmult_assoc;
      rewrite <- Rinv_l_sym; [ idtac | discrR ]; rewrite Rmult_1_r;
        replace (2 * k + (1 - k)) with (1 + k); [ idtac | ring ].
  elim H; intros.
  apply Rplus_lt_compat_l; assumption.
  unfold Un_cv in H0; cut (0 < (1 - k) / 2).
  intro; elim (H0 ((1 - k) / 2) H1); intros.
  exists x; intros.
  assert (H4 := H2 n H3).
  unfold R_dist in H4; rewrite <- Rabs_Rabsolu;
    replace (Rabs (An (S n) / An n)) with (Rabs (An (S n) / An n) - k + k);
    [ idtac | ring ];
    apply Rle_lt_trans with (Rabs (Rabs (An (S n) / An n) - k) + Rabs k).
  apply Rabs_triang.
  rewrite (Rabs_right k).
  apply Rplus_lt_reg_r with (- k); rewrite <- (Rplus_comm k);
    repeat rewrite <- Rplus_assoc; rewrite Rplus_opp_l;
      repeat rewrite Rplus_0_l; apply H4.
  apply Rle_ge; elim H; intros; assumption.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  apply Rplus_lt_reg_r with k; rewrite Rplus_0_r; elim H; intros;
    replace (k + (1 - k)) with 1; [ assumption | ring ].
  apply Rinv_0_lt_compat; prove_sup0.
Qed.

(**********)
Lemma growing_ineq :
  forall (Un:nat -> R) (l:R),
    Un_growing Un -> Un_cv Un l -> forall n:nat, Un n <= l.
Proof.
  intros; case (total_order_T (Un n) l); intro.
  elim s; intro.
  left; assumption.
  right; assumption.
  cut (0 < Un n - l).
  intro; unfold Un_cv in H0; unfold R_dist in H0.
  elim (H0 (Un n - l) H1); intros N1 H2.
  set (N := max n N1).
  cut (Un n - l <= Un N - l).
  intro; cut (Un N - l < Un n - l).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H3 H4)).
  apply Rle_lt_trans with (Rabs (Un N - l)).
  apply RRle_abs.
  apply H2.
  unfold ge, N in |- *; apply le_max_r.
  unfold Rminus in |- *; do 2 rewrite <- (Rplus_comm (- l));
    apply Rplus_le_compat_l.
  apply tech9.
  assumption.
  unfold N in |- *; apply le_max_l.
  apply Rplus_lt_reg_r with l.
  rewrite Rplus_0_r.
  replace (l + (Un n - l)) with (Un n); [ assumption | ring ].
Qed.

(** Un->l => (-Un) -> (-l) *)
Lemma CV_opp :
  forall (An:nat -> R) (l:R), Un_cv An l -> Un_cv (opp_seq An) (- l).
Proof.
  intros An l.
  unfold Un_cv in |- *; unfold R_dist in |- *; intros.
  elim (H eps H0); intros.
  exists x; intros.
  unfold opp_seq in |- *; replace (- An n - - l) with (- (An n - l));
    [ rewrite Rabs_Ropp | ring ].
  apply H1; assumption.
Qed.

(**********)
Lemma decreasing_ineq :
  forall (Un:nat -> R) (l:R),
    Un_decreasing Un -> Un_cv Un l -> forall n:nat, l <= Un n.
Proof.
  intros.
  assert (H1 := decreasing_growing _ H).
  assert (H2 := CV_opp _ _ H0).
  assert (H3 := growing_ineq _ _ H1 H2).
  apply Ropp_le_cancel.
  unfold opp_seq in H3; apply H3.
Qed.

(**********)
Lemma CV_minus :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i - Bn i) (l1 - l2).
Proof.
  intros.
  replace (fun i:nat => An i - Bn i) with (fun i:nat => An i + opp_seq Bn i).
  unfold Rminus in |- *; apply CV_plus.
  assumption.
  apply CV_opp; assumption.
  unfold Rminus, opp_seq in |- *; reflexivity.
Qed.

(** Un -> +oo *)
Definition cv_infty (Un:nat -> R) : Prop :=
  forall M:R,  exists N : nat, (forall n:nat, (N <= n)%nat -> M < Un n).

(** Un -> +oo => /Un -> O *)
Lemma cv_infty_cv_R0 :
  forall Un:nat -> R,
    (forall n:nat, Un n <> 0) -> cv_infty Un -> Un_cv (fun n:nat => / Un n) 0.
Proof.
  unfold cv_infty, Un_cv in |- *; unfold R_dist in |- *; intros.
  elim (H0 (/ eps)); intros N0 H2.
  exists N0; intros.
  unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r;
    rewrite (Rabs_Rinv _ (H n)).
  apply Rmult_lt_reg_l with (Rabs (Un n)).
  apply Rabs_pos_lt; apply H.
  rewrite <- Rinv_r_sym.
  apply Rmult_lt_reg_l with (/ eps).
  apply Rinv_0_lt_compat; assumption.
  rewrite Rmult_1_r; rewrite (Rmult_comm (/ eps)); rewrite Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; apply Rlt_le_trans with (Un n).
  apply H2; assumption.
  apply RRle_abs.
  red in |- *; intro; rewrite H4 in H1; elim (Rlt_irrefl _ H1).
  apply Rabs_no_R0; apply H.
Qed.

(**********)
Lemma decreasing_prop :
  forall (Un:nat -> R) (m n:nat),
    Un_decreasing Un -> (m <= n)%nat -> Un n <= Un m.
Proof.
  unfold Un_decreasing in |- *; intros.
  induction  n as [| n Hrecn].
  induction  m as [| m Hrecm].
  right; reflexivity.
  elim (le_Sn_O _ H0).
  cut ((m <= n)%nat \/ m = S n).
  intro; elim H1; intro.
  apply Rle_trans with (Un n).
  apply H.
  apply Hrecn; assumption.
  rewrite H2; right; reflexivity.
  inversion H0; [ right; reflexivity | left; assumption ].
Qed.

(** |x|^n/n! -> 0 *)
Lemma cv_speed_pow_fact :
  forall x:R, Un_cv (fun n:nat => x ^ n / INR (fact n)) 0.
Proof.
  intro;
    cut
      (Un_cv (fun n:nat => Rabs x ^ n / INR (fact n)) 0 ->
        Un_cv (fun n:nat => x ^ n / INR (fact n)) 0).
  intro; apply H.
  unfold Un_cv in |- *; unfold R_dist in |- *; intros; case (Req_dec x 0);
    intro.
  exists 1%nat; intros.
  rewrite H1; unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r;
    rewrite Rabs_R0; rewrite pow_ne_zero;
      [ unfold Rdiv in |- *; rewrite Rmult_0_l; rewrite Rabs_R0; assumption
        | red in |- *; intro; rewrite H3 in H2; elim (le_Sn_n _ H2) ].
  assert (H2 := Rabs_pos_lt x H1); set (M := up (Rabs x)); cut (0 <= M)%Z.
  intro; elim (IZN M H3); intros M_nat H4.
  set (Un := fun n:nat => Rabs x ^ (M_nat + n) / INR (fact (M_nat + n))).
  cut (Un_cv Un 0); unfold Un_cv in |- *; unfold R_dist in |- *; intros.
  elim (H5 eps H0); intros N H6.
  exists (M_nat + N)%nat; intros;
    cut (exists p : nat, (p >= N)%nat /\ n = (M_nat + p)%nat).
  intro; elim H8; intros p H9.
  elim H9; intros; rewrite H11; unfold Un in H6; apply H6; assumption.
  exists (n - M_nat)%nat.
  split.
  unfold ge in |- *; apply (fun p n m:nat => plus_le_reg_l n m p) with M_nat;
    rewrite <- le_plus_minus.
  assumption.
  apply le_trans with (M_nat + N)%nat.
  apply le_plus_l.
  assumption.
  apply le_plus_minus; apply le_trans with (M_nat + N)%nat;
    [ apply le_plus_l | assumption ].
  set (Vn := fun n:nat => Rabs x * (Un 0%nat / INR (S n))).
  cut (1 <= M_nat)%nat.
  intro; cut (forall n:nat, 0 < Un n).
  intro; cut (Un_decreasing Un).
  intro; cut (forall n:nat, Un (S n) <= Vn n).
  intro; cut (Un_cv Vn 0).
  unfold Un_cv in |- *; unfold R_dist in |- *; intros.
  elim (H10 eps0 H5); intros N1 H11.
  exists (S N1); intros.
  cut (forall n:nat, 0 < Vn n).
  intro; apply Rle_lt_trans with (Rabs (Vn (pred n) - 0)).
  repeat rewrite Rabs_right.
  unfold Rminus in |- *; rewrite Ropp_0; do 2 rewrite Rplus_0_r;
    replace n with (S (pred n)).
  apply H9.
  inversion H12; simpl in |- *; reflexivity.
  apply Rle_ge; unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; left;
    apply H13.
  apply Rle_ge; unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; left;
    apply H7.
  apply H11; unfold ge in |- *; apply le_S_n; replace (S (pred n)) with n;
    [ unfold ge in H12; exact H12 | inversion H12; simpl in |- *; reflexivity ].
  intro; apply Rlt_le_trans with (Un (S n0)); [ apply H7 | apply H9 ].
  cut (cv_infty (fun n:nat => INR (S n))).
  intro; cut (Un_cv (fun n:nat => / INR (S n)) 0).
  unfold Un_cv, R_dist in |- *; intros; unfold Vn in |- *.
  cut (0 < eps1 / (Rabs x * Un 0%nat)).
  intro; elim (H11 _ H13); intros N H14.
  exists N; intros;
    replace (Rabs x * (Un 0%nat / INR (S n)) - 0) with
    (Rabs x * Un 0%nat * (/ INR (S n) - 0));
    [ idtac | unfold Rdiv in |- *; ring ].
  rewrite Rabs_mult; apply Rmult_lt_reg_l with (/ Rabs (Rabs x * Un 0%nat)).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt.
  apply prod_neq_R0.
  apply Rabs_no_R0; assumption.
  assert (H16 := H7 0%nat); red in |- *; intro; rewrite H17 in H16;
    elim (Rlt_irrefl _ H16).
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l.
  replace (/ Rabs (Rabs x * Un 0%nat) * eps1) with (eps1 / (Rabs x * Un 0%nat)).
  apply H14; assumption.
  unfold Rdiv in |- *; rewrite (Rabs_right (Rabs x * Un 0%nat)).
  apply Rmult_comm.
  apply Rle_ge; apply Rmult_le_pos.
  apply Rabs_pos.
  left; apply H7.
  apply Rabs_no_R0.
  apply prod_neq_R0;
    [ apply Rabs_no_R0; assumption
      | assert (H16 := H7 0%nat); red in |- *; intro; rewrite H17 in H16;
        elim (Rlt_irrefl _ H16) ].
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat; apply Rmult_lt_0_compat.
  apply Rabs_pos_lt; assumption.
  apply H7.
  apply (cv_infty_cv_R0 (fun n:nat => INR (S n))).
  intro; apply not_O_INR; discriminate.
  assumption.
  unfold cv_infty in |- *; intro; case (total_order_T M0 0); intro.
  elim s; intro.
  exists 0%nat; intros.
  apply Rlt_trans with 0; [ assumption | apply lt_INR_0; apply lt_O_Sn ].
  exists 0%nat; intros; rewrite b; apply lt_INR_0; apply lt_O_Sn.
  set (M0_z := up M0).
  assert (H10 := archimed M0).
  cut (0 <= M0_z)%Z.
  intro; elim (IZN _ H11); intros M0_nat H12.
  exists M0_nat; intros.
  apply Rlt_le_trans with (IZR M0_z).
  elim H10; intros; assumption.
  rewrite H12; rewrite <- INR_IZR_INZ; apply le_INR.
  apply le_trans with n; [ assumption | apply le_n_Sn ].
  apply le_IZR; left; simpl in |- *; unfold M0_z in |- *;
    apply Rlt_trans with M0; [ assumption | elim H10; intros; assumption ].
  intro; apply Rle_trans with (Rabs x * Un n * / INR (S n)).
  unfold Un in |- *; replace (M_nat + S n)%nat with (M_nat + n + 1)%nat.
  rewrite pow_add; replace (Rabs x ^ 1) with (Rabs x);
    [ idtac | simpl in |- *; ring ].
  unfold Rdiv in |- *; rewrite <- (Rmult_comm (Rabs x));
    repeat rewrite Rmult_assoc; repeat apply Rmult_le_compat_l.
  apply Rabs_pos.
  left; apply pow_lt; assumption.
  replace (M_nat + n + 1)%nat with (S (M_nat + n)).
  rewrite fact_simpl; rewrite mult_comm; rewrite mult_INR;
    rewrite Rinv_mult_distr.
  apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply lt_INR_0; apply neq_O_lt; red in |- *;
    intro; assert (H10 := sym_eq H9); elim (fact_neq_0 _ H10).
  left; apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat; apply lt_INR_0; apply lt_O_Sn.
  apply lt_INR; apply lt_n_S.
  pattern n at 1 in |- *; replace n with (0 + n)%nat; [ idtac | reflexivity ].
  apply plus_lt_compat_r.
  apply lt_le_trans with 1%nat; [ apply lt_O_Sn | assumption ].
  apply INR_fact_neq_0.
  apply not_O_INR; discriminate.
  ring_nat.
  ring_nat.
  unfold Vn in |- *; rewrite Rmult_assoc; unfold Rdiv in |- *;
    rewrite (Rmult_comm (Un 0%nat)); rewrite (Rmult_comm (Un n)).
  repeat apply Rmult_le_compat_l.
  apply Rabs_pos.
  left; apply Rinv_0_lt_compat; apply lt_INR_0; apply lt_O_Sn.
  apply decreasing_prop; [ assumption | apply le_O_n ].
  unfold Un_decreasing in |- *; intro; unfold Un in |- *.
  replace (M_nat + S n)%nat with (M_nat + n + 1)%nat.
  rewrite pow_add; unfold Rdiv in |- *; rewrite Rmult_assoc;
    apply Rmult_le_compat_l.
  left; apply pow_lt; assumption.
  replace (Rabs x ^ 1) with (Rabs x); [ idtac | simpl in |- *; ring ].
  replace (M_nat + n + 1)%nat with (S (M_nat + n)).
  apply Rmult_le_reg_l with (INR (fact (S (M_nat + n)))).
  apply lt_INR_0; apply neq_O_lt; red in |- *; intro; assert (H9 := sym_eq H8);
    elim (fact_neq_0 _ H9).
  rewrite (Rmult_comm (Rabs x)); rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l.
  rewrite fact_simpl; rewrite mult_INR; rewrite Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; apply Rle_trans with (INR M_nat).
  left; rewrite INR_IZR_INZ.
  rewrite <- H4; assert (H8 := archimed (Rabs x)); elim H8; intros; assumption.
  apply le_INR; omega.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  ring_nat.
  ring_nat.
  intro; unfold Un in |- *; unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  apply pow_lt; assumption.
  apply Rinv_0_lt_compat; apply lt_INR_0; apply neq_O_lt; red in |- *; intro;
    assert (H8 := sym_eq H7); elim (fact_neq_0 _ H8).
  clear Un Vn; apply INR_le; simpl in |- *.
  induction  M_nat as [| M_nat HrecM_nat].
  assert (H6 := archimed (Rabs x)); fold M in H6; elim H6; intros.
  rewrite H4 in H7; rewrite <- INR_IZR_INZ in H7.
  simpl in H7; elim (Rlt_irrefl _ (Rlt_trans _ _ _ H2 H7)).
  replace 1 with (INR 1); [ apply le_INR | reflexivity ]; apply le_n_S;
    apply le_O_n.
  apply le_IZR; simpl in |- *; left; apply Rlt_trans with (Rabs x).
  assumption.
  elim (archimed (Rabs x)); intros; assumption.
  unfold Un_cv in |- *; unfold R_dist in |- *; intros; elim (H eps H0); intros.
  exists x0; intros;
    apply Rle_lt_trans with (Rabs (Rabs x ^ n / INR (fact n) - 0)).
  unfold Rminus in |- *; rewrite Ropp_0; do 2 rewrite Rplus_0_r;
    rewrite (Rabs_right (Rabs x ^ n / INR (fact n))).
  unfold Rdiv in |- *; rewrite Rabs_mult; rewrite (Rabs_right (/ INR (fact n))).
  rewrite RPow_abs; right; reflexivity.
  apply Rle_ge; left; apply Rinv_0_lt_compat; apply lt_INR_0; apply neq_O_lt;
    red in |- *; intro; assert (H4 := sym_eq H3); elim (fact_neq_0 _ H4).
  apply Rle_ge; unfold Rdiv in |- *; apply Rmult_le_pos.
  case (Req_dec x 0); intro.
  rewrite H3; rewrite Rabs_R0.
  induction  n as [| n Hrecn];
    [ simpl in |- *; left; apply Rlt_0_1
      | simpl in |- *; rewrite Rmult_0_l; right; reflexivity ].
  left; apply pow_lt; apply Rabs_pos_lt; assumption.
  left; apply Rinv_0_lt_compat; apply lt_INR_0; apply neq_O_lt; red in |- *;
    intro; assert (H4 := sym_eq H3); elim (fact_neq_0 _ H4).
  apply H1; assumption.
Qed.
