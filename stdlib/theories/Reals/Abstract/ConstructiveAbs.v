(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

Require Import QArith.
Require Import Qabs.
Require Import ConstructiveReals.

Local Open Scope ConstructiveReals.

(** Properties of constructive absolute value (defined in
    ConstructiveReals.CRabs).
    Definition of minimum, maximum and their properties.

    WARNING: this file is experimental and likely to change in future releases.
*)

#[global]
Instance CRabs_morph
  : forall {R : ConstructiveReals},
    CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CReq R)) (CRabs R).
Proof.
  intros R x y [H H0]. split.
  - rewrite <- CRabs_def. split.
    + apply (CRle_trans _ x).
      * apply H.
      * pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
        apply H1. apply CRle_refl.
    + apply (CRle_trans _ (CRopp R x)).
      * intro abs.
        apply CRopp_lt_cancel in abs. contradiction.
      * pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
        apply H1. apply CRle_refl.
  - rewrite <- CRabs_def. split.
    + apply (CRle_trans _ y).
      * apply H0.
      * pose proof (CRabs_def R y (CRabs R y)) as [_ H1].
        apply H1. apply CRle_refl.
    + apply (CRle_trans _ (CRopp R y)).
      * intro abs.
        apply CRopp_lt_cancel in abs. contradiction.
      * pose proof (CRabs_def R y (CRabs R y)) as [_ H1].
        apply H1. apply CRle_refl.
Qed.

Add Parametric Morphism {R : ConstructiveReals} : (CRabs R)
    with signature CReq R ==> CReq R
      as CRabs_morph_prop.
Proof.
  intros. apply CRabs_morph, H.
Qed.

Lemma CRabs_right : forall {R : ConstructiveReals} (x : CRcarrier R),
    0 <= x -> CRabs R x == x.
Proof.
  intros. split.
  - pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
    apply H1, CRle_refl.
  - rewrite <- CRabs_def. split.
    + apply CRle_refl.
    + apply (CRle_trans _ 0). 2: exact H.
      apply (CRle_trans _ (CRopp R 0)).
      * intro abs. apply CRopp_lt_cancel in abs. contradiction.
      * apply (CRplus_le_reg_l 0).
        apply (CRle_trans _ 0).
        -- apply CRplus_opp_r.
        -- apply CRplus_0_r.
Qed.

Lemma CRabs_opp : forall {R : ConstructiveReals} (x : CRcarrier R),
    CRabs R (- x) == CRabs R x.
Proof.
  intros. split.
  - rewrite <- CRabs_def. split.
    + pose proof (CRabs_def R (CRopp R x) (CRabs R (CRopp R x))) as [_ H1].
      specialize (H1 (CRle_refl (CRabs R (CRopp R x)))) as [_ H1].
      apply (CRle_trans _ (CRopp R (CRopp R x))).
      2: exact H1. apply (CRopp_involutive x).
    + pose proof (CRabs_def R (CRopp R x) (CRabs R (CRopp R x))) as [_ H1].
      apply H1, CRle_refl.
  - rewrite <- CRabs_def. split.
    + pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
      apply H1, CRle_refl.
    + apply (CRle_trans _ x).
      * apply CRopp_involutive.
      * pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
        apply H1, CRle_refl.
Qed.

Lemma CRabs_minus_sym : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRabs R (x - y) == CRabs R (y - x).
Proof.
  intros R x y. setoid_replace (x - y) with (-(y-x)).
  - rewrite CRabs_opp. reflexivity.
  - unfold CRminus.
    rewrite CRopp_plus_distr, CRplus_comm, CRopp_involutive.
    reflexivity.
Qed.

Lemma CRabs_left : forall {R : ConstructiveReals} (x : CRcarrier R),
    x <= 0 -> CRabs R x == - x.
Proof.
  intros. rewrite <- CRabs_opp. apply CRabs_right.
  rewrite <- CRopp_0. apply CRopp_ge_le_contravar, H.
Qed.

Lemma CRabs_triang : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRabs R (x + y) <= CRabs R x + CRabs R y.
Proof.
  intros. rewrite <- CRabs_def. split.
  - apply (CRle_trans _ (CRplus R (CRabs R x) y)).
    + apply CRplus_le_compat_r.
      pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
      apply H1, CRle_refl.
    + apply CRplus_le_compat_l.
      pose proof (CRabs_def R y (CRabs R y)) as [_ H1].
      apply H1, CRle_refl.
  - apply (CRle_trans _ (CRplus R (CRopp R x) (CRopp R y))).
    + apply CRopp_plus_distr.
    + apply (CRle_trans _ (CRplus R (CRabs R x) (CRopp R y))).
      * apply CRplus_le_compat_r.
        pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
        apply H1, CRle_refl.
      * apply CRplus_le_compat_l.
        pose proof (CRabs_def R y (CRabs R y)) as [_ H1].
        apply H1, CRle_refl.
Qed.

Lemma CRabs_le : forall {R : ConstructiveReals} (a b:CRcarrier R),
    (-b <= a /\ a <= b) -> CRabs R a <= b.
Proof.
  intros. pose proof (CRabs_def R a b) as [H0 _].
  apply H0. split.
  - apply H.
  - destruct H.
    rewrite <- (CRopp_involutive b).
    apply CRopp_ge_le_contravar. exact H.
Qed.

Lemma CRabs_triang_inv : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRabs R x - CRabs R y <= CRabs R (x - y).
Proof.
  intros. apply (CRplus_le_reg_r (CRabs R y)).
  unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l.
  rewrite CRplus_0_r.
  apply (CRle_trans _ (CRabs R (x - y + y))).
  - setoid_replace (x - y + y) with x.
    + apply CRle_refl.
    + unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l.
      rewrite CRplus_0_r. reflexivity.
  - apply CRabs_triang.
Qed.

Lemma CRabs_triang_inv2 : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRabs R (CRabs R x - CRabs R y) <= CRabs R (x - y).
Proof.
  intros. apply CRabs_le. split.
  2: apply CRabs_triang_inv.
  apply (CRplus_le_reg_r (CRabs R y)).
  unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l.
  rewrite CRplus_0_r. fold (x - y).
  rewrite CRplus_comm, CRabs_minus_sym.
  apply (CRle_trans _ _ _ (CRabs_triang_inv y (y-x))).
  setoid_replace (y - (y - x)) with x.
  - apply CRle_refl.
  - unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
    rewrite CRplus_opp_r, CRplus_0_l. apply CRopp_involutive.
Qed.

Lemma CR_of_Q_abs : forall {R : ConstructiveReals} (q : Q),
    CRabs R (CR_of_Q R q) == CR_of_Q R (Qabs q).
Proof.
  intros. destruct (Qlt_le_dec 0 q).
  - apply (CReq_trans _ (CR_of_Q R q)).
    + apply CRabs_right. apply CR_of_Q_le. apply Qlt_le_weak, q0.
    + apply CR_of_Q_morph. symmetry. apply Qabs_pos, Qlt_le_weak, q0.
  - apply (CReq_trans _ (CR_of_Q R (-q))).
    + apply (CReq_trans _ (CRabs R (CRopp R (CR_of_Q R q)))).
      * apply CReq_sym, CRabs_opp.
      * apply (CReq_trans _ (CRopp R (CR_of_Q R q))).
        -- apply CRabs_right.
           apply (CRle_trans _ (CR_of_Q R (-q))).
           ++ apply CR_of_Q_le.
              apply (Qplus_le_l _ _ q). ring_simplify. exact q0.
           ++ apply CR_of_Q_opp.
        -- apply CReq_sym, CR_of_Q_opp.
    + apply CR_of_Q_morph; symmetry; apply Qabs_neg, q0.
Qed.

Lemma CRle_abs : forall {R : ConstructiveReals} (x : CRcarrier R),
    x <= CRabs R x.
Proof.
  intros. pose proof (CRabs_def R x (CRabs R x)) as [_ H].
  apply H, CRle_refl.
Qed.

Lemma CRabs_pos : forall {R : ConstructiveReals} (x : CRcarrier R),
    0 <= CRabs R x.
Proof.
  intros. intro abs. destruct (CRltLinear R). clear p.
  specialize (s _ x _ abs). destruct s.
  - exact (CRle_abs x c).
  - rewrite CRabs_left in abs.
    + rewrite <- CRopp_0 in abs. apply CRopp_lt_cancel in abs.
      exact (CRlt_asym _ _ abs c).
    + apply CRlt_asym, c.
Qed.

Lemma CRabs_appart_0 : forall {R : ConstructiveReals} (x : CRcarrier R),
    0 < CRabs R x -> x ≶ 0.
Proof.
  intros. destruct (CRltLinear R). clear p.
  pose proof (s _ x _ H) as [pos|neg].
  - right. exact pos.
  - left.
    destruct (CR_Q_dense R _ _ neg) as [q [H0 H1]].
    destruct (Qlt_le_dec 0 q).
    + destruct (s (CR_of_Q R (-q)) x 0).
      * apply CR_of_Q_lt.
        apply (Qplus_lt_l _ _ q). ring_simplify. exact q0.
      * exfalso. pose proof (CRabs_def R x (CR_of_Q R q)) as [H2 _].
        apply H2.
        -- clear H2. split.
           ++ apply CRlt_asym, H0.
           ++ rewrite <- Qopp_involutive, CR_of_Q_opp.
              apply CRopp_ge_le_contravar, CRlt_asym, c.
        -- exact H1.
      * exact c.
    + apply (CRlt_le_trans _ _ _ H0).
      apply CR_of_Q_le. exact q0.
Qed.


(* The proof by cases on the signs of x and y applies constructively,
   because of the positivity hypotheses. *)
Lemma CRabs_mult : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRabs R (x * y) == CRabs R x * CRabs R y.
Proof.
  intro R.
  assert (forall (x y : CRcarrier R),
             x ≶ 0
             -> y ≶ 0
             -> CRabs R (x * y) == CRabs R x * CRabs R y) as prep.
  { intros. destruct H, H0.
    - rewrite CRabs_right, CRabs_left, CRabs_left.
      + rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r, CRopp_involutive.
        reflexivity.
      + apply CRlt_asym, c0.
      + apply CRlt_asym, c.
      + setoid_replace (x*y) with (- x * - y).
        * apply CRlt_asym, CRmult_lt_0_compat.
          -- rewrite <- CRopp_0. apply CRopp_gt_lt_contravar, c.
          -- rewrite <- CRopp_0. apply CRopp_gt_lt_contravar, c0.
        * rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r, CRopp_involutive.
          reflexivity.
    - rewrite CRabs_left, CRabs_left, CRabs_right.
      + rewrite <- CRopp_mult_distr_l. reflexivity.
      + apply CRlt_asym, c0.
      + apply CRlt_asym, c.
      + rewrite <- (CRmult_0_l y).
        apply CRmult_le_compat_r_half.
        * exact c0.
        * apply CRlt_asym, c.
    - rewrite CRabs_left, CRabs_right, CRabs_left.
      + rewrite <- CRopp_mult_distr_r. reflexivity.
      + apply CRlt_asym, c0.
      + apply CRlt_asym, c.
      + rewrite <- (CRmult_0_r x).
        apply CRmult_le_compat_l_half.
        * exact c.
        * apply CRlt_asym, c0.
    - rewrite CRabs_right, CRabs_right, CRabs_right.
      + reflexivity.
      + apply CRlt_asym, c0.
      + apply CRlt_asym, c.
      + apply CRlt_asym, CRmult_lt_0_compat; assumption. }
  split.
  - intro abs.
    assert (0 < CRabs R x * CRabs R y).
    { apply (CRle_lt_trans _ (CRabs R (x*y))).
      - apply CRabs_pos.
      - exact abs. }
    pose proof (CRmult_pos_appart_zero _ _ H).
    rewrite CRmult_comm in H.
    apply CRmult_pos_appart_zero in H.
    destruct H. 2: apply (CRabs_pos y c).
    destruct H0. 2: apply (CRabs_pos x c0).
    apply CRabs_appart_0 in c.
    apply CRabs_appart_0 in c0.
    rewrite (prep x y) in abs.
    + exact (CRlt_asym _ _ abs abs).
    + exact c0.
    + exact c.
  - intro abs.
    assert (0 < CRabs R (x * y)).
    { apply (CRle_lt_trans _ (CRabs R x * CRabs R y)).
      - rewrite <- (CRmult_0_l (CRabs R y)).
        apply CRmult_le_compat_r.
        + apply CRabs_pos.
        + apply CRabs_pos.
      - exact abs. }
    apply CRabs_appart_0 in H. destruct H.
    + apply CRopp_gt_lt_contravar in c.
      rewrite CRopp_0, CRopp_mult_distr_l in c.
      pose proof (CRmult_pos_appart_zero _ _ c).
      rewrite CRmult_comm in c.
      apply CRmult_pos_appart_zero in c.
      rewrite (prep x y) in abs.
      * exact (CRlt_asym _ _ abs abs).
      * destruct H.
        -- left. apply CRopp_gt_lt_contravar in c0.
           rewrite CRopp_involutive, CRopp_0 in c0. exact c0.
        -- right. apply CRopp_gt_lt_contravar in c0.
           rewrite CRopp_involutive, CRopp_0 in c0. exact c0.
      * destruct c.
        -- right. exact c.
        -- left. exact c.
    + pose proof (CRmult_pos_appart_zero _ _ c).
      rewrite CRmult_comm in c.
      apply CRmult_pos_appart_zero in c.
      rewrite (prep x y) in abs.
      * exact (CRlt_asym _ _ abs abs).
      * destruct H.
        -- right. exact c0.
        -- left. exact c0.
      * destruct c.
        -- right. exact c.
        -- left. exact c.
Qed.

Lemma CRabs_lt : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRabs _ x < y -> prod (x < y) (-x < y).
Proof.
  split.
  - apply (CRle_lt_trans _ _ _ (CRle_abs x)), H.
  - apply (CRle_lt_trans _ _ _ (CRle_abs (-x))).
    rewrite CRabs_opp. exact H.
Qed.

Lemma CRabs_def1 : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x < y -> -x < y -> CRabs _ x < y.
Proof.
  intros. destruct (CRltLinear R), p.
  destruct (s x (CRabs R x) y H). 2: exact c0.
  rewrite CRabs_left.
  - exact H0.
  - intro abs.
    rewrite CRabs_right in c0.
    + exact (CRlt_asym x x c0 c0).
    + apply CRlt_asym, abs.
Qed.

Lemma CRabs_def2 : forall {R : ConstructiveReals} (x a:CRcarrier R),
    CRabs _ x <= a -> (x <= a) /\ (- a <= x).
Proof.
  split.
  - exact (CRle_trans _ _ _ (CRle_abs _) H).
  - rewrite <- (CRopp_involutive x).
    apply CRopp_ge_le_contravar.
    rewrite <- CRabs_opp in H.
    exact (CRle_trans _ _ _ (CRle_abs _) H).
Qed.
