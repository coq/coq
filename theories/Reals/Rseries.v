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
Require Import Compare.
Local Open Scope R_scope.

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
  Fixpoint Rmax_N (N:nat) : R :=
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
    unfold EUn; split with (Un 0); split with 0%nat; trivial.
  Qed.

(*********)
  Lemma Un_in_EUn : forall n:nat, EUn (Un n).
  Proof.
    intro; unfold EUn; split with n; trivial.
  Qed.

(*********)
  Lemma Un_bound_imp :
    forall x:R, (forall n:nat, Un n <= x) -> is_upper_bound EUn x.
  Proof.
    intros; unfold is_upper_bound; intros; unfold EUn in H0; elim H0;
      clear H0; intros; generalize (H x1); intro; rewrite <- H0 in H1;
        trivial.
  Qed.

(*********)
  Lemma growing_prop :
    forall n m:nat, Un_growing -> (n >= m)%nat -> Un n >= Un m.
  Proof.
    double induction n m; intros.
    unfold Rge; right; trivial.
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
    rewrite y; unfold Rge; right; trivial.
    unfold ge in H0; generalize (H0 (S n0) H1 (lt_le_S n0 n1 y)); intro;
      unfold Un_growing in H1;
        apply
          (Rge_trans (Un (S n1)) (Un n1) (Un (S n0))
            (Rle_ge (Un n1) (Un (S n1)) (H1 n1)) H3).
  Qed.

(*********)
  Lemma Un_cv_crit_lub : Un_growing -> forall l, is_lub EUn l -> Un_cv l.
  Proof.
    intros Hug l H eps Heps.

    cut (exists N, Un N > l - eps).
    intros (N, H3).
    exists N.
    intros n H4.
    unfold R_dist.
    rewrite Rabs_left1, Ropp_minus_distr.
    apply Rplus_lt_reg_l with (Un n - eps).
    apply Rlt_le_trans with (Un N).
    now replace (Un n - eps + (l - Un n)) with (l - eps) by ring.
    replace (Un n - eps + eps) with (Un n) by ring.
    apply Rge_le.
    now apply growing_prop.
    apply Rle_minus.
    apply (proj1 H).
    now exists n.

    assert (Hi2pn: forall n, 0 < (/ 2)^n).
    clear. intros n.
    apply pow_lt.
    apply Rinv_0_lt_compat.
    now apply (IZR_lt 0 2).

    pose (test := fun n => match Rle_lt_dec (Un n) (l - eps) with left _ => false | right _ => true end).
    pose (sum := let fix aux n := match n with S n' => aux n' +
      if test n' then (/ 2)^n else 0 | O => 0 end in aux).

    assert (Hsum': forall m n, sum m <= sum (m + n)%nat <= sum m + (/2)^m - (/2)^(m + n)).
    clearbody test.
    clear -Hi2pn.
    intros m.
    induction n.
    rewrite<- plus_n_O.
    ring_simplify (sum m + (/ 2) ^ m - (/ 2) ^ m).
    split ; apply Rle_refl.
    rewrite <- plus_n_Sm.
    simpl.
    split.
    apply Rle_trans with (sum (m + n)%nat + 0).
    rewrite Rplus_0_r.
    apply IHn.
    apply Rplus_le_compat_l.
    case (test (m + n)%nat).
    apply Rlt_le.
    exact (Hi2pn (S (m + n))).
    apply Rle_refl.
    apply Rle_trans with (sum (m + n)%nat + / 2 * (/ 2) ^ (m + n)).
    apply Rplus_le_compat_l.
    case (test (m + n)%nat).
    apply Rle_refl.
    apply Rlt_le.
    exact (Hi2pn (S (m + n))).
    apply Rplus_le_reg_r with (-(/ 2 * (/ 2) ^ (m + n))).
    rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
    apply Rle_trans with (1 := proj2 IHn).
    apply Req_le.
    field.

    assert (Hsum: forall n, 0 <= sum n <= 1 - (/2)^n).
    intros N.
    generalize (Hsum' O N).
    simpl.
    now rewrite Rplus_0_l.

    destruct (completeness (fun x : R => exists n : nat, x = sum n)) as (m, (Hm1, Hm2)).
    exists 1.
    intros x (n, H1).
    rewrite H1.
    apply Rle_trans with (1 := proj2 (Hsum n)).
    apply Rlt_le.
    apply Rplus_lt_reg_l with ((/2)^n - 1).
    now ring_simplify.
    exists 0. now exists O.

    destruct (Rle_or_lt m 0) as [[Hm|Hm]|Hm].
    elim Rlt_not_le with (1 := Hm).
    apply Hm1.
    now exists O.

    assert (Hs0: forall n, sum n = 0).
    intros n.
    specialize (Hm1 (sum n) (ex_intro _ _ (eq_refl _))).
    apply Rle_antisym with (2 := proj1 (Hsum n)).
    now rewrite <- Hm.

    assert (Hub: forall n, Un n <= l - eps).
    intros n.
    generalize (eq_refl (sum (S n))).
    simpl sum at 1.
    rewrite 2!Hs0, Rplus_0_l.
    unfold test.
    destruct Rle_lt_dec. easy.
    intros H'.
    elim Rgt_not_eq with (2 := H').
    exact (Hi2pn (S n)).

    clear -Heps H Hub.
    destruct H as (_, H).
    refine (False_ind _ (Rle_not_lt _ _ (H (l - eps) _) _)).
    intros x (n, H1).
    now rewrite H1.
    apply Rplus_lt_reg_l with (eps - l).
    now ring_simplify.

    assert (Rabs (/2) < 1).
    rewrite Rabs_pos_eq.
    rewrite <- Rinv_1.
    apply Rinv_lt_contravar.
    rewrite Rmult_1_l.
    now apply (IZR_lt 0 2).
    now apply (IZR_lt 1 2).
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    now apply (IZR_lt 0 2).
    destruct (pow_lt_1_zero (/2) H0 m Hm) as [N H4].
    exists N.
    apply Rnot_le_lt.
    intros H5.
    apply Rlt_not_le with (1 := H4 _ (le_refl _)).
    rewrite Rabs_pos_eq. 2: now apply Rlt_le.
    apply Hm2.
    intros x (n, H6).
    rewrite H6. clear x H6.

    assert (Hs: sum N = 0).
    clear H4.
    induction N.
    easy.
    simpl.
    assert (H6: Un N <= l - eps).
    apply Rle_trans with (2 := H5).
    apply Rge_le.
    apply growing_prop ; try easy.
    apply le_n_Sn.
    rewrite (IHN H6), Rplus_0_l.
    unfold test.
    destruct Rle_lt_dec as [Hle|Hlt].
    apply eq_refl.
    now elim Rlt_not_le with (1 := Hlt).

    destruct (le_or_lt N n) as [Hn|Hn].
    rewrite le_plus_minus with (1 := Hn).
    apply Rle_trans with (1 := proj2 (Hsum' N (n - N)%nat)).
    rewrite Hs, Rplus_0_l.
    set (k := (N + (n - N))%nat).
    apply Rlt_le.
    apply Rplus_lt_reg_l with ((/2)^k - (/2)^N).
    now ring_simplify.
    apply Rle_trans with (sum N).
    rewrite le_plus_minus with (1 := Hn).
    rewrite plus_Snm_nSm.
    exact (proj1 (Hsum' _ _)).
    rewrite Hs.
    now apply Rlt_le.
  Qed.

(*********)
  Lemma Un_cv_crit : Un_growing -> bound EUn ->  exists l : R, Un_cv l.
  Proof.
    intros Hug Heub.
    exists (proj1_sig (completeness EUn Heub EUn_noempty)).
    destruct (completeness EUn Heub EUn_noempty) as (l, H).
    now apply Un_cv_crit_lub.
  Qed.

(*********)
  Lemma finite_greater :
    forall N:nat,  exists M : R, (forall n:nat, (n <= N)%nat -> Un n <= M).
  Proof.
    intro; induction  N as [| N HrecN].
    split with (Un 0); intros; rewrite (le_n_O_eq n H);
      apply (Req_le (Un n) (Un n) (eq_refl (Un n))).
    elim HrecN; clear HrecN; intros; split with (Rmax (Un (S N)) x); intros;
      elim (Rmax_Rle (Un (S N)) x (Un n)); intros; clear H1;
        inversion H0.
    rewrite <- H1; rewrite <- H1 in H2;
      apply
        (H2 (or_introl (Un n <= x) (Req_le (Un n) (Un n) (eq_refl (Un n))))).
    apply (H2 (or_intror (Un n <= Un (S N)) (H n H3))).
  Qed.

(*********)
  Lemma cauchy_bound : Cauchy_crit -> bound EUn.
  Proof.
    unfold Cauchy_crit, bound; intros; unfold is_upper_bound;
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
  intros; unfold Pser; unfold infinite_sum; intros;
    elim (Req_dec x 0).
  intros; exists 0%nat; intros; rewrite H1; rewrite Rminus_0_r; rewrite Rinv_1;
    cut (sum_f_R0 (fun n0:nat => 1 * 0 ^ n0) n = 1).
  intros; rewrite H3; rewrite R_dist_eq; auto.
  elim n; simpl.
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
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  unfold R_dist; rewrite <- Rabs_mult.
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
  intro H8; rewrite H8; simpl; rewrite Rabs_mult;
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
  intros; rewrite H9; unfold Rle; right; reflexivity.
  ring.
  assumption.
  ring.
  ring.
  ring.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  ring; ring.
  elim n; simpl.
  ring.
  intros; rewrite H5.
  ring.
  apply Rmult_lt_0_compat.
  auto.
  apply Rmult_lt_0_compat.
  apply Rabs_pos_lt.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  apply Rabs_pos_lt.
  apply Rinv_neq_0_compat.
  assumption.
Qed.

(* Convergence is preserved after shifting the indices. *)
Lemma CV_shift : 
  forall f k l, Un_cv (fun n => f (n + k)%nat) l -> Un_cv f l.
intros f' k l cvfk eps ep; destruct (cvfk eps ep) as [N Pn].
exists (N + k)%nat; intros n nN; assert (tmp: (n = (n - k) + k)%nat).
 rewrite Nat.sub_add;[ | apply le_trans with (N + k)%nat]; auto with arith.
rewrite tmp; apply Pn; apply Nat.le_add_le_sub_r; assumption.
Qed.

Lemma CV_shift' : 
  forall f k l, Un_cv f l -> Un_cv (fun n => f (n + k)%nat) l.
intros f' k l cvf eps ep; destruct (cvf eps ep) as [N Pn].
exists N; intros n nN; apply Pn; auto with arith.
Qed.

(* Growing property is preserved after shifting the indices (one way only) *)

Lemma Un_growing_shift : 
   forall k un, Un_growing un -> Un_growing (fun n => un (n + k)%nat).
Proof.
intros k un P n; apply P.
Qed.
