(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
    Definition of minimum, maximum and their properties. *)

Instance CRabs_morph
  : forall {R : ConstructiveReals},
    CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CReq R)) (CRabs R).
Proof.
  intros R x y [H H0]. split.
  - rewrite <- CRabs_def. split.
    + apply (CRle_trans _ x). apply H.
      pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
      apply H1. apply CRle_refl.
    + apply (CRle_trans _ (CRopp R x)). intro abs.
      apply CRopp_lt_cancel in abs. contradiction.
      pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
      apply H1. apply CRle_refl.
  - rewrite <- CRabs_def. split.
    + apply (CRle_trans _ y). apply H0.
      pose proof (CRabs_def R y (CRabs R y)) as [_ H1].
      apply H1. apply CRle_refl.
    + apply (CRle_trans _ (CRopp R y)). intro abs.
      apply CRopp_lt_cancel in abs. contradiction.
      pose proof (CRabs_def R y (CRabs R y)) as [_ H1].
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
  - rewrite <- CRabs_def. split. apply CRle_refl.
    apply (CRle_trans _ (CRzero R)). 2: exact H.
    apply (CRle_trans _ (CRopp R (CRzero R))).
    intro abs. apply CRopp_lt_cancel in abs. contradiction.
    apply (CRplus_le_reg_l (CRzero R)).
    apply (CRle_trans _ (CRzero R)). apply CRplus_opp_r.
    apply CRplus_0_r.
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
    + apply (CRle_trans _ x). apply CRopp_involutive.
      pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
      apply H1, CRle_refl.
Qed.

Lemma CRabs_minus_sym : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRabs R (x - y) == CRabs R (y - x).
Proof.
  intros R x y. setoid_replace (x - y) with (-(y-x)).
  rewrite CRabs_opp. reflexivity. unfold CRminus.
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
    apply CRplus_le_compat_r.
    pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
    apply H1, CRle_refl.
    apply CRplus_le_compat_l.
    pose proof (CRabs_def R y (CRabs R y)) as [_ H1].
    apply H1, CRle_refl.
  - apply (CRle_trans _ (CRplus R (CRopp R x) (CRopp R y))).
    apply CRopp_plus_distr.
    apply (CRle_trans _ (CRplus R (CRabs R x) (CRopp R y))).
    apply CRplus_le_compat_r.
    pose proof (CRabs_def R x (CRabs R x)) as [_ H1].
    apply H1, CRle_refl.
    apply CRplus_le_compat_l.
    pose proof (CRabs_def R y (CRabs R y)) as [_ H1].
    apply H1, CRle_refl.
Qed.

Lemma CRabs_le : forall {R : ConstructiveReals} (a b:CRcarrier R),
    (-b <= a /\ a <= b) -> CRabs R a <= b.
Proof.
  intros. pose proof (CRabs_def R a b) as [H0 _].
  apply H0. split. apply H. destruct H.
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
  setoid_replace (x - y + y) with x. apply CRle_refl.
  unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l.
  rewrite CRplus_0_r. reflexivity.
  apply CRabs_triang.
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
  setoid_replace (y - (y - x)) with x. apply CRle_refl.
  unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
  rewrite CRplus_opp_r, CRplus_0_l. apply CRopp_involutive.
Qed.

Lemma CR_of_Q_abs : forall {R : ConstructiveReals} (q : Q),
    CRabs R (CR_of_Q R q) == CR_of_Q R (Qabs q).
Proof.
  intros. destruct (Qlt_le_dec 0 q).
  - apply (CReq_trans _ (CR_of_Q R q)).
    apply CRabs_right. apply (CRle_trans _ (CR_of_Q R 0)).
    apply CR_of_Q_zero. apply CR_of_Q_le. apply Qlt_le_weak, q0.
    apply CR_of_Q_morph. symmetry. apply Qabs_pos, Qlt_le_weak, q0.
  - apply (CReq_trans _ (CR_of_Q R (-q))).
    apply (CReq_trans _ (CRabs R (CRopp R (CR_of_Q R q)))).
    apply CReq_sym, CRabs_opp.
    2: apply CR_of_Q_morph; symmetry; apply Qabs_neg, q0.
    apply (CReq_trans _ (CRopp R (CR_of_Q R q))).
    2: apply CReq_sym, CR_of_Q_opp.
    apply CRabs_right. apply (CRle_trans _ (CR_of_Q R 0)).
    apply CR_of_Q_zero.
    apply (CRle_trans _ (CR_of_Q R (-q))). apply CR_of_Q_le.
    apply (Qplus_le_l _ _ q). ring_simplify. exact q0.
    apply CR_of_Q_opp.
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
  exact (CRle_abs x c). rewrite CRabs_left in abs.
  rewrite <- CRopp_0 in abs. apply CRopp_lt_cancel in abs.
  exact (CRlt_asym _ _ abs c). apply CRlt_asym, c.
Qed.

Lemma CRabs_appart_0 : forall {R : ConstructiveReals} (x : CRcarrier R),
    0 < CRabs R x -> CRapart R x 0.
Proof.
  intros. destruct (CRltLinear R). clear p.
  pose proof (s _ x _ H) as [pos|neg].
  right. exact pos. left.
  destruct (CR_Q_dense R _ _ neg) as [q [H0 H1]].
  destruct (Qlt_le_dec 0 q).
  - destruct (s (CR_of_Q R (-q)) x 0).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt.
    apply (Qplus_lt_l _ _ q). ring_simplify. exact q0.
    exfalso. pose proof (CRabs_def R x (CR_of_Q R q)) as [H2 _].
    apply H2. clear H2. split. apply CRlt_asym, H0.
    2: exact H1. rewrite <- Qopp_involutive, CR_of_Q_opp.
    apply CRopp_ge_le_contravar, CRlt_asym, c. exact c.
  - apply (CRlt_le_trans _ _ _ H0).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. exact q0.
Qed.


(* The proof by cases on the signs of x and y applies constructively,
   because of the positivity hypotheses. *)
Lemma CRabs_mult : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRabs R (x * y) == CRabs R x * CRabs R y.
Proof.
  intro R.
  assert (forall (x y : CRcarrier R),
             CRapart R x 0
             -> CRapart R y 0
             -> CRabs R (x * y) == CRabs R x * CRabs R y) as prep.
  { intros. destruct H, H0.
    + rewrite CRabs_right, CRabs_left, CRabs_left.
      rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r, CRopp_involutive.
      reflexivity.
      apply CRlt_asym, c0. apply CRlt_asym, c.
      setoid_replace (x*y) with (- x * - y).
      apply CRlt_asym, CRmult_lt_0_compat.
      rewrite <- CRopp_0. apply CRopp_gt_lt_contravar, c.
      rewrite <- CRopp_0. apply CRopp_gt_lt_contravar, c0.
      rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r, CRopp_involutive.
      reflexivity.
    + rewrite CRabs_left, CRabs_left, CRabs_right.
      rewrite <- CRopp_mult_distr_l. reflexivity.
      apply CRlt_asym, c0. apply CRlt_asym, c.
      rewrite <- (CRmult_0_l y).
      apply CRmult_le_compat_r_half. exact c0.
      apply CRlt_asym, c.
    + rewrite CRabs_left, CRabs_right, CRabs_left.
      rewrite <- CRopp_mult_distr_r. reflexivity.
      apply CRlt_asym, c0. apply CRlt_asym, c.
      rewrite <- (CRmult_0_r x).
      apply CRmult_le_compat_l_half.
      exact c. apply CRlt_asym, c0.
    + rewrite CRabs_right, CRabs_right, CRabs_right. reflexivity.
      apply CRlt_asym, c0. apply CRlt_asym, c.
      apply CRlt_asym, CRmult_lt_0_compat; assumption. }
  split.
  - intro abs.
    assert (0 < CRabs R x * CRabs R y).
    { apply (CRle_lt_trans _ (CRabs R (x*y))).
      apply CRabs_pos. exact abs. }
    pose proof (CRmult_pos_appart_zero _ _ H).
    rewrite CRmult_comm in H.
    apply CRmult_pos_appart_zero in H.
    destruct H. 2: apply (CRabs_pos y c).
    destruct H0. 2: apply (CRabs_pos x c0).
    apply CRabs_appart_0 in c.
    apply CRabs_appart_0 in c0.
    rewrite (prep x y) in abs.
    exact (CRlt_asym _ _ abs abs). exact c0. exact c.
  - intro abs.
    assert (0 < CRabs R (x * y)).
    { apply (CRle_lt_trans _ (CRabs R x * CRabs R y)).
      rewrite <- (CRmult_0_l (CRabs R y)).
      apply CRmult_le_compat_r.
      apply CRabs_pos. apply CRabs_pos. exact abs. }
    apply CRabs_appart_0 in H. destruct H.
    + apply CRopp_gt_lt_contravar in c.
      rewrite CRopp_0, CRopp_mult_distr_l in c.
      pose proof (CRmult_pos_appart_zero _ _ c).
      rewrite CRmult_comm in c.
      apply CRmult_pos_appart_zero in c.
      rewrite (prep x y) in abs.
      exact (CRlt_asym _ _ abs abs).
      destruct H. left. apply CRopp_gt_lt_contravar in c0.
      rewrite CRopp_involutive, CRopp_0 in c0. exact c0.
      right. apply CRopp_gt_lt_contravar in c0.
      rewrite CRopp_involutive, CRopp_0 in c0. exact c0.
      destruct c. right. exact c. left. exact c.
    + pose proof (CRmult_pos_appart_zero _ _ c).
      rewrite CRmult_comm in c.
      apply CRmult_pos_appart_zero in c.
      rewrite (prep x y) in abs.
      exact (CRlt_asym _ _ abs abs).
      destruct H. right. exact c0. left. exact c0.
      destruct c. right. exact c. left. exact c.
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
  rewrite CRabs_left. exact H0. intro abs.
  rewrite CRabs_right in c0. exact (CRlt_asym x x c0 c0).
  apply CRlt_asym, abs.
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


(* Minimum *)

Definition CRmin {R : ConstructiveReals} (x y : CRcarrier R) : CRcarrier R
  := (x + y - CRabs _ (y - x)) * CR_of_Q _ (1#2).

Lemma CRmin_lt_r : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRmin x y < y -> CRmin x y == x.
Proof.
  intros. unfold CRmin. unfold CRmin in H.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  left; apply CR_of_Q_pos; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l, CRmult_1_r.
  rewrite CRabs_right. unfold CRminus.
  rewrite CRopp_plus_distr, CRplus_assoc, <- (CRplus_assoc y).
  rewrite CRplus_opp_r, CRplus_0_l, CRopp_involutive. reflexivity.
  apply (CRmult_lt_compat_r (CR_of_Q R 2)) in H.
  2: apply CR_of_Q_pos; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult in H.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q in H. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r in H.
  rewrite CRmult_comm, (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_r,
  CRmult_1_l in H.
  intro abs. rewrite CRabs_left in H.
  unfold CRminus in H.
  rewrite CRopp_involutive, CRplus_comm in H.
  rewrite CRplus_assoc, <- (CRplus_assoc (-x)), CRplus_opp_l in H.
  rewrite CRplus_0_l in H. exact (CRlt_asym _ _ H H).
  apply CRlt_asym, abs.
Qed.

Add Parametric Morphism {R : ConstructiveReals} : CRmin
    with signature (CReq R) ==> (CReq R) ==> (CReq R)
      as CRmin_morph.
Proof.
  intros. unfold CRmin.
  apply CRmult_morph. 2: reflexivity.
  unfold CRminus.
  rewrite H, H0. reflexivity.
Qed.

Instance CRmin_morphT
  : forall {R : ConstructiveReals},
    CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CMorphisms.respectful (CReq R) (CReq R))) (@CRmin R).
Proof.
  intros R x y H z t H0.
  rewrite H, H0. reflexivity.
Qed.

Lemma CRmin_l : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRmin x y <= x.
Proof.
  intros. unfold CRmin.
  apply (CRmult_le_reg_r (CR_of_Q R 2)).
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  unfold CRminus. rewrite CRplus_assoc. apply CRplus_le_compat_l.
  apply (CRplus_le_reg_r (CRabs _ (y + - x)+ -x)).
  rewrite CRplus_assoc, <- (CRplus_assoc (-CRabs _ (y + - x))).
  rewrite CRplus_opp_l, CRplus_0_l.
  rewrite (CRplus_comm x), CRplus_assoc, CRplus_opp_l, CRplus_0_r.
  apply CRle_abs.
Qed.

Lemma CRmin_r : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRmin x y <= y.
Proof.
  intros. unfold CRmin.
  apply (CRmult_le_reg_r (CR_of_Q R 2)).
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  rewrite (CRplus_comm x).
  unfold CRminus. rewrite CRplus_assoc. apply CRplus_le_compat_l.
  apply (CRplus_le_reg_l (-x)).
  rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
  rewrite <- (CRopp_involutive y), <- CRopp_plus_distr, <- CRopp_plus_distr.
  apply CRopp_ge_le_contravar. rewrite CRabs_opp, CRplus_comm.
  apply CRle_abs.
Qed.

Lemma CRnegPartAbsMin : forall {R : ConstructiveReals} (x : CRcarrier R),
    CRmin 0 x == (x - CRabs _ x) * (CR_of_Q _ (1#2)).
Proof.
  intros. unfold CRmin. unfold CRminus. rewrite CRplus_0_l.
  apply CRmult_morph. 2: reflexivity. rewrite CRopp_0, CRplus_0_r. reflexivity.
Qed.

Lemma CRmin_sym : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRmin x y == CRmin y x.
Proof.
  intros. unfold CRmin. apply CRmult_morph. 2: reflexivity.
  rewrite CRabs_minus_sym. unfold CRminus.
  rewrite (CRplus_comm x y). reflexivity.
Qed.

Lemma CRmin_mult :
  forall {R : ConstructiveReals} (p q r : CRcarrier R),
    0 <= r -> CRmin (r * p) (r * q) == r * CRmin p q.
Proof.
  intros R p q r H. unfold CRmin.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  rewrite CRabs_mult.
  rewrite (CRabs_right r). 2: exact H.
  rewrite <- CRmult_assoc. apply CRmult_morph. 2: reflexivity.
  unfold CRminus. rewrite CRopp_mult_distr_r.
  do 2 rewrite <- CRmult_plus_distr_l. reflexivity.
  unfold CRminus. rewrite CRopp_mult_distr_r.
  rewrite <- CRmult_plus_distr_l. reflexivity.
Qed.

Lemma CRmin_plus : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    x + CRmin y z == CRmin (x + y) (x + z).
Proof.
  intros. unfold CRmin.
  unfold CRminus. setoid_replace (x + z + - (x + y)) with (z-y).
  apply (CRmult_eq_reg_r (CR_of_Q _ 2)).
  left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_plus_distr_r.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  do 3 rewrite (CRplus_assoc x). apply CRplus_morph. reflexivity.
  do 2 rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
  rewrite (CRplus_comm x). apply CRplus_assoc.
  rewrite CRopp_plus_distr. rewrite <- CRplus_assoc.
  apply CRplus_morph. 2: reflexivity.
  rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
  apply CRplus_0_l.
Qed.

Lemma CRmin_left : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x <= y -> CRmin x y == x.
Proof.
  intros. unfold CRmin.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  rewrite CRabs_right. unfold CRminus. rewrite CRopp_plus_distr.
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l. apply CRopp_involutive.
  rewrite <- (CRplus_opp_r x). apply CRplus_le_compat.
  exact H. apply CRle_refl.
Qed.

Lemma CRmin_right : forall {R : ConstructiveReals} (x y : CRcarrier R),
    y <= x -> CRmin x y == y.
Proof.
  intros. unfold CRmin.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  rewrite CRabs_left. unfold CRminus. do 2 rewrite CRopp_plus_distr.
  rewrite (CRplus_comm x y).
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  do 2 rewrite CRopp_involutive.
  rewrite CRplus_comm, CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
  rewrite <- (CRplus_opp_r x). apply CRplus_le_compat.
  exact H. apply CRle_refl.
Qed.

Lemma CRmin_lt : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    z < x -> z < y -> z < CRmin x y.
Proof.
  intros. unfold CRmin.
  apply (CRmult_lt_reg_r (CR_of_Q R 2)).
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  apply (CRplus_lt_reg_l _ (CRabs _ (y - x) - (z*CR_of_Q R 2))).
  unfold CRminus. rewrite CRplus_assoc. rewrite CRplus_opp_l, CRplus_0_r.
  rewrite (CRplus_comm (CRabs R (y + - x))).
  rewrite (CRplus_comm (x+y)), CRplus_assoc.
  rewrite <- (CRplus_assoc (CRabs R (y + - x))), CRplus_opp_r, CRplus_0_l.
  rewrite <- (CRplus_comm (x+y)).
  apply CRabs_def1.
  - unfold CRminus. rewrite <- (CRplus_comm y), CRplus_assoc.
    apply CRplus_lt_compat_l.
    apply (CRplus_lt_reg_l R (-x)).
    rewrite CRopp_mult_distr_l.
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l.
    rewrite CRmult_1_r. apply CRplus_le_lt_compat.
    apply CRlt_asym.
    apply CRopp_gt_lt_contravar, H.
    apply CRopp_gt_lt_contravar, H.
  - rewrite CRopp_plus_distr, CRopp_involutive.
    rewrite CRplus_comm, CRplus_assoc.
    apply CRplus_lt_compat_l.
    apply (CRplus_lt_reg_l R (-y)).
    rewrite CRopp_mult_distr_l.
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l.
    rewrite CRmult_1_r. apply CRplus_le_lt_compat.
    apply CRlt_asym.
    apply CRopp_gt_lt_contravar, H0.
    apply CRopp_gt_lt_contravar, H0.
Qed.

Lemma CRmin_contract : forall {R : ConstructiveReals} (x y a : CRcarrier R),
    CRabs _ (CRmin x a - CRmin y a) <= CRabs _ (x - y).
Proof.
  intros. unfold CRmin.
  unfold CRminus. rewrite CRopp_mult_distr_l, <- CRmult_plus_distr_r.
  rewrite (CRabs_morph
             _ ((x - y + (CRabs _ (a - y) - CRabs _ (a - x))) * CR_of_Q R (1 # 2))).
  rewrite CRabs_mult, (CRabs_right (CR_of_Q R (1 # 2))).
  2: rewrite <- CR_of_Q_zero; apply CR_of_Q_le; discriminate.
  apply (CRle_trans _
           ((CRabs _ (x - y) * 1 + CRabs _ (x-y) * 1)
              * CR_of_Q R (1 # 2))).
  apply CRmult_le_compat_r.
  rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  apply (CRle_trans
           _ (CRabs _ (x - y) + CRabs _ (CRabs _ (a - y) - CRabs _ (a - x)))).
  apply CRabs_triang. rewrite CRmult_1_r. apply CRplus_le_compat_l.
  rewrite (CRabs_morph (x-y) ((a-y)-(a-x))).
  apply CRabs_triang_inv2.
  unfold CRminus. rewrite (CRplus_comm (a + - y)).
  rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
  rewrite CRplus_comm, CRopp_plus_distr, <- CRplus_assoc.
  rewrite CRplus_opp_r, CRopp_involutive, CRplus_0_l.
  reflexivity.
  rewrite <- CRmult_plus_distr_l, <- CR_of_Q_one.
  rewrite <- (CR_of_Q_plus R 1 1).
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 + 1) * (1 # 2))%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r. apply CRle_refl.
  unfold CRminus. apply CRmult_morph. 2: reflexivity.
  do 4 rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite <- CRplus_assoc. rewrite CRplus_comm, CRopp_plus_distr.
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite CRopp_plus_distr. rewrite (CRplus_comm (-a)).
  rewrite CRplus_assoc, <- (CRplus_assoc (-a)), CRplus_opp_l.
  rewrite CRplus_0_l, CRopp_involutive. reflexivity.
Qed.

Lemma CRmin_glb : forall {R : ConstructiveReals} (x y z:CRcarrier R),
    z <= x -> z <= y -> z <= CRmin x y.
Proof.
  intros. unfold CRmin.
  apply (CRmult_le_reg_r (CR_of_Q R 2)).
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  apply (CRplus_le_reg_l (CRabs _ (y-x) - (z*CR_of_Q R 2))).
  unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
  rewrite (CRplus_comm (CRabs R (y + - x) + - (z * CR_of_Q R 2))).
  rewrite CRplus_assoc, <- (CRplus_assoc (- CRabs R (y + - x))).
  rewrite CRplus_opp_l, CRplus_0_l.
  apply CRabs_le. split.
  - do 2 rewrite CRopp_plus_distr.
    rewrite CRopp_involutive, (CRplus_comm y), CRplus_assoc.
    apply CRplus_le_compat_l, (CRplus_le_reg_l y).
    rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l.
    rewrite CRmult_1_r. apply CRplus_le_compat; exact H0.
  - rewrite (CRplus_comm x), CRplus_assoc. apply CRplus_le_compat_l.
    apply (CRplus_le_reg_l (-x)).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    rewrite CRopp_mult_distr_l.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l.
    rewrite CRmult_1_r.
    apply CRplus_le_compat; apply CRopp_ge_le_contravar; exact H.
Qed.

Lemma CRmin_assoc : forall {R : ConstructiveReals} (a b c : CRcarrier R),
    CRmin a (CRmin b c) == CRmin (CRmin a b) c.
Proof.
  split.
  - apply CRmin_glb.
    + apply (CRle_trans _ (CRmin a b)).
      apply CRmin_l. apply CRmin_l.
    + apply CRmin_glb.
      apply (CRle_trans _ (CRmin a b)).
      apply CRmin_l. apply CRmin_r. apply CRmin_r.
  - apply CRmin_glb.
    + apply CRmin_glb. apply CRmin_l.
      apply (CRle_trans _ (CRmin b c)).
      apply CRmin_r. apply CRmin_l.
    + apply (CRle_trans _ (CRmin b c)).
      apply CRmin_r. apply CRmin_r.
Qed.

Lemma CRlt_min : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    z < CRmin x y -> prod (z < x) (z < y).
Proof.
  intros. destruct (CR_Q_dense R _ _ H) as [q qmaj].
  destruct qmaj.
  split.
  - apply (CRlt_le_trans _ (CR_of_Q R q) _ c).
    intro abs. apply (CRlt_asym _ _ c0).
    apply (CRle_lt_trans _ x). apply CRmin_l. exact abs.
  - apply (CRlt_le_trans _ (CR_of_Q R q) _ c).
    intro abs. apply (CRlt_asym _ _ c0).
    apply (CRle_lt_trans _ y). apply CRmin_r. exact abs.
Qed.



(* Maximum *)

Definition CRmax {R : ConstructiveReals} (x y : CRcarrier R) : CRcarrier R
  := (x + y + CRabs _ (y - x)) * CR_of_Q _ (1#2).

Add Parametric Morphism {R : ConstructiveReals} : CRmax
    with signature (CReq R) ==> (CReq R) ==> (CReq R)
      as CRmax_morph.
Proof.
  intros. unfold CRmax.
  apply CRmult_morph. 2: reflexivity. unfold CRminus.
  rewrite H, H0. reflexivity.
Qed.

Instance CRmax_morphT
  : forall {R : ConstructiveReals},
    CMorphisms.Proper
      (CMorphisms.respectful (CReq R) (CMorphisms.respectful (CReq R) (CReq R))) (@CRmax R).
Proof.
  intros R x y H z t H0.
  rewrite H, H0. reflexivity.
Qed.

Lemma CRmax_lub : forall {R : ConstructiveReals} (x y z:CRcarrier R),
    x <= z -> y <= z -> CRmax x y <= z.
Proof.
  intros. unfold CRmax.
  apply (CRmult_le_reg_r (CR_of_Q _ 2)). rewrite <- CR_of_Q_zero.
  apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  apply (CRplus_le_reg_l (-x-y)).
  rewrite <- CRplus_assoc. unfold CRminus.
  rewrite <- CRopp_plus_distr, CRplus_opp_l, CRplus_0_l.
  apply CRabs_le. split.
  - repeat rewrite CRopp_plus_distr.
    do 2 rewrite CRopp_involutive.
    rewrite (CRplus_comm x), CRplus_assoc. apply CRplus_le_compat_l.
    apply (CRplus_le_reg_l (-x)).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
    rewrite CRopp_plus_distr.
    apply CRplus_le_compat; apply CRopp_ge_le_contravar; assumption.
  - rewrite (CRplus_comm y), CRopp_plus_distr, CRplus_assoc.
    apply CRplus_le_compat_l.
    apply (CRplus_le_reg_l y).
    rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
    apply CRplus_le_compat; assumption.
Qed.

Lemma CRmax_l : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x <= CRmax x y.
Proof.
  intros. unfold CRmax.
  apply (CRmult_le_reg_r (CR_of_Q R 2)). rewrite <- CR_of_Q_zero.
  apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  setoid_replace 2%Q with (1+1)%Q. rewrite CR_of_Q_plus, CR_of_Q_one.
  rewrite CRmult_plus_distr_l, CRmult_1_r, CRplus_assoc.
  apply CRplus_le_compat_l.
  apply (CRplus_le_reg_l (-y)).
  rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
  rewrite CRabs_minus_sym, CRplus_comm.
  apply CRle_abs. reflexivity.
Qed.

Lemma CRmax_r : forall {R : ConstructiveReals} (x y : CRcarrier R),
    y <= CRmax x y.
Proof.
  intros. unfold CRmax.
  apply (CRmult_le_reg_r (CR_of_Q _ 2)). rewrite <- CR_of_Q_zero.
  apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  rewrite (CRplus_comm x).
  rewrite CRplus_assoc. apply CRplus_le_compat_l.
  apply (CRplus_le_reg_l (-x)).
  rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
  rewrite CRplus_comm. apply CRle_abs.
Qed.

Lemma CRposPartAbsMax : forall {R : ConstructiveReals} (x : CRcarrier R),
    CRmax 0 x == (x + CRabs _ x) * (CR_of_Q R (1#2)).
Proof.
  intros. unfold CRmax. unfold CRminus. rewrite CRplus_0_l.
  apply CRmult_morph. 2: reflexivity. rewrite CRopp_0, CRplus_0_r. reflexivity.
Qed.

Lemma CRmax_sym : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRmax x y == CRmax y x.
Proof.
  intros. unfold CRmax.
  rewrite CRabs_minus_sym. apply CRmult_morph.
  2: reflexivity. rewrite (CRplus_comm x y). reflexivity.
Qed.

Lemma CRmax_plus : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    x + CRmax y z == CRmax (x + y) (x + z).
Proof.
  intros. unfold CRmax.
  setoid_replace (x + z - (x + y)) with (z-y).
  apply (CRmult_eq_reg_r (CR_of_Q _ 2)).
  left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_plus_distr_r.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  rewrite CRmult_1_r.
  do 3 rewrite (CRplus_assoc x). apply CRplus_morph. reflexivity.
  do 2 rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
  rewrite (CRplus_comm x). apply CRplus_assoc.
  unfold CRminus. rewrite CRopp_plus_distr. rewrite <- CRplus_assoc.
  apply CRplus_morph. 2: reflexivity.
  rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
  apply CRplus_0_l.
Qed.

Lemma CRmax_left : forall {R : ConstructiveReals} (x y : CRcarrier R),
    y <= x -> CRmax x y == x.
Proof.
  intros. unfold CRmax.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite CRabs_left. unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive.
  rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l. reflexivity.
  rewrite <- (CRplus_opp_r x). apply CRplus_le_compat_r. exact H.
Qed.

Lemma CRmax_right : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x <= y -> CRmax x y == y.
Proof.
  intros. unfold CRmax.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CR_of_Q_one, CRmult_1_r.
  rewrite (CRplus_comm x y).
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite CRabs_right. unfold CRminus. rewrite CRplus_comm.
  rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
  rewrite <- (CRplus_opp_r x). apply CRplus_le_compat_r. exact H.
Qed.

Lemma CRmax_contract : forall {R : ConstructiveReals} (x y a : CRcarrier R),
    CRabs _ (CRmax x a - CRmax y a) <= CRabs _ (x - y).
Proof.
  intros. unfold CRmax.
  rewrite (CRabs_morph
             _ ((x - y + (CRabs _ (a - x) - CRabs _ (a - y))) * CR_of_Q R (1 # 2))).
  rewrite CRabs_mult, (CRabs_right (CR_of_Q R (1 # 2))).
  2: rewrite <- CR_of_Q_zero; apply CR_of_Q_le; discriminate.
  apply (CRle_trans
           _ ((CRabs _ (x - y) * 1 + CRabs _ (x-y) * 1)
              * CR_of_Q R (1 # 2))).
  apply CRmult_le_compat_r.
  rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  apply (CRle_trans
           _ (CRabs _ (x - y) + CRabs _ (CRabs _ (a - x) - CRabs _ (a - y)))).
  apply CRabs_triang. rewrite CRmult_1_r. apply CRplus_le_compat_l.
  rewrite (CRabs_minus_sym x y).
  rewrite (CRabs_morph (y-x) ((a-x)-(a-y))).
  apply CRabs_triang_inv2.
  unfold CRminus. rewrite (CRplus_comm (a + - x)).
  rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
  rewrite CRplus_comm, CRopp_plus_distr, <- CRplus_assoc.
  rewrite CRplus_opp_r, CRopp_involutive, CRplus_0_l.
  reflexivity.
  rewrite <- CRmult_plus_distr_l, <- CR_of_Q_one.
  rewrite <- (CR_of_Q_plus R 1 1).
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 + 1) * (1 # 2))%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r. apply CRle_refl.
  unfold CRminus. rewrite CRopp_mult_distr_l.
  rewrite <- CRmult_plus_distr_r. apply CRmult_morph. 2: reflexivity.
  do 4 rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite <- CRplus_assoc. rewrite CRplus_comm, CRopp_plus_distr.
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite CRopp_plus_distr. rewrite (CRplus_comm (-a)).
  rewrite CRplus_assoc, <- (CRplus_assoc (-a)), CRplus_opp_l.
  rewrite CRplus_0_l. apply CRplus_comm.
Qed.

Lemma CRmax_lub_lt : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    x < z -> y < z -> CRmax x y < z.
Proof.
  intros. unfold CRmax.
  apply (CRmult_lt_reg_r (CR_of_Q R 2)).
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CR_of_Q_one, CRmult_1_r.
  apply (CRplus_lt_reg_l _ (-y -x)). unfold CRminus.
  rewrite CRplus_assoc, <- (CRplus_assoc (-x)), <- (CRplus_assoc (-x)).
  rewrite CRplus_opp_l, CRplus_0_l, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
  apply CRabs_def1.
  - rewrite (CRplus_comm y), (CRplus_comm (-y)), CRplus_assoc.
    apply CRplus_lt_compat_l.
    apply (CRplus_lt_reg_l _ y).
    rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l.
    rewrite CRmult_1_r. apply CRplus_le_lt_compat.
    apply CRlt_asym, H0. exact H0.
  - rewrite CRopp_plus_distr, CRopp_involutive.
    rewrite CRplus_assoc. apply CRplus_lt_compat_l.
    apply (CRplus_lt_reg_l _ x).
    rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l.
    rewrite CRmult_1_r. apply CRplus_le_lt_compat.
    apply CRlt_asym, H. exact H.
Qed.

Lemma CRmax_assoc : forall {R : ConstructiveReals} (a b c : CRcarrier R),
    CRmax a (CRmax b c) == CRmax (CRmax a b) c.
Proof.
  split.
  - apply CRmax_lub.
    + apply CRmax_lub. apply CRmax_l.
      apply (CRle_trans _ (CRmax b c)).
      apply CRmax_l. apply CRmax_r.
    + apply (CRle_trans _ (CRmax b c)).
      apply CRmax_r. apply CRmax_r.
  - apply CRmax_lub.
    + apply (CRle_trans _ (CRmax a b)).
      apply CRmax_l. apply CRmax_l.
    + apply CRmax_lub.
      apply (CRle_trans _ (CRmax a b)).
      apply CRmax_r. apply CRmax_l. apply CRmax_r.
Qed.

Lemma CRmax_min_mult_neg :
  forall {R : ConstructiveReals} (p q r:CRcarrier R),
    r <= 0 -> CRmax (r * p) (r * q) == r * CRmin p q.
Proof.
  intros R p q r H. unfold CRmin, CRmax.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  rewrite CRabs_mult.
  rewrite (CRabs_left r), <- CRmult_assoc.
  apply CRmult_morph. 2: reflexivity. unfold CRminus.
  rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r,
  CRmult_plus_distr_l, CRmult_plus_distr_l.
  reflexivity. exact H.
  unfold CRminus. rewrite CRmult_plus_distr_l, CRopp_mult_distr_r. reflexivity.
Qed.

Lemma CRlt_max : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    CRmax x y < z -> prod (x < z) (y < z).
Proof.
  intros. destruct (CR_Q_dense R _ _ H) as [q qmaj].
  destruct qmaj.
  split.
  - apply (CRlt_le_trans _ (CR_of_Q R q)).
    apply (CRle_lt_trans _ (CRmax x y)). apply CRmax_l. exact c.
    apply CRlt_asym, c0.
  - apply (CRlt_le_trans _ (CR_of_Q R q)).
    apply (CRle_lt_trans _ (CRmax x y)). apply CRmax_r. exact c.
    apply CRlt_asym, c0.
Qed.

Lemma CRmax_mult :
  forall {R : ConstructiveReals} (p q r:CRcarrier R),
    0 <= r -> CRmax (r * p) (r * q) == r * CRmax p q.
Proof.
  intros R p q r H. unfold CRmin, CRmax.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  rewrite CRabs_mult.
  rewrite (CRabs_right r), <- CRmult_assoc.
  apply CRmult_morph. 2: reflexivity.
  rewrite CRmult_plus_distr_l, CRmult_plus_distr_l.
  reflexivity. exact H.
  unfold CRminus. rewrite CRmult_plus_distr_l, CRopp_mult_distr_r. reflexivity.
Qed.

Lemma CRmin_max_mult_neg :
  forall {R : ConstructiveReals} (p q r:CRcarrier R),
    r <= 0 -> CRmin (r * p) (r * q) == r * CRmax p q.
Proof.
  intros R p q r H. unfold CRmin, CRmax.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  rewrite CRabs_mult.
  rewrite (CRabs_left r), <- CRmult_assoc.
  apply CRmult_morph. 2: reflexivity. unfold CRminus.
  rewrite CRopp_mult_distr_l, CRopp_involutive,
  CRmult_plus_distr_l, CRmult_plus_distr_l.
  reflexivity. exact H.
  unfold CRminus. rewrite CRmult_plus_distr_l, CRopp_mult_distr_r. reflexivity.
Qed.
