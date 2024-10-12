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
Require Import ConstructiveAbs.
Require Import ConstructiveRealsMorphisms.

Local Open Scope ConstructiveReals.

(** Definition and properties of minimum and maximum.

    WARNING: this file is experimental and likely to change in future releases.
 *)


(* Minimum *)

Definition CRmin {R : ConstructiveReals} (x y : CRcarrier R) : CRcarrier R
  := (x + y - CRabs _ (y - x)) * CR_of_Q _ (1#2).

Lemma CRmin_lt_r : forall {R : ConstructiveReals} (x y : CRcarrier R),
    CRmin x y < y -> CRmin x y == x.
Proof.
  intros. unfold CRmin. unfold CRmin in H.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  - left; apply CR_of_Q_pos; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    rewrite (CR_of_Q_plus R 1 1), CRmult_plus_distr_l, CRmult_1_r.
    rewrite CRabs_right.
    + unfold CRminus.
      rewrite CRopp_plus_distr, CRplus_assoc, <- (CRplus_assoc y).
      rewrite CRplus_opp_r, CRplus_0_l, CRopp_involutive. reflexivity.
    + apply (CRmult_lt_compat_r (CR_of_Q R 2)) in H.
      2: apply CR_of_Q_pos; reflexivity.
      intro abs. contradict H.
      apply (CRle_trans _ (x + y - CRabs R (y - x))).
      * rewrite CRabs_left. 2: apply CRlt_asym, abs.
        unfold CRminus. rewrite CRopp_involutive, CRplus_comm.
        rewrite CRplus_assoc, <- (CRplus_assoc (-x)), CRplus_opp_l.
        rewrite CRplus_0_l, (CR_of_Q_plus R 1 1), CRmult_plus_distr_l.
        rewrite CRmult_1_r. apply CRle_refl.
      * rewrite CRmult_assoc, <- CR_of_Q_mult.
        setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
        rewrite CRmult_1_r. apply CRle_refl.
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

#[global]
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
  - apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
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
  - apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
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
  - rewrite CRabs_mult.
    rewrite (CRabs_right r). 2: exact H.
    rewrite <- CRmult_assoc. apply CRmult_morph. 2: reflexivity.
    unfold CRminus. rewrite CRopp_mult_distr_r.
    do 2 rewrite <- CRmult_plus_distr_l. reflexivity.
  - unfold CRminus. rewrite CRopp_mult_distr_r.
    rewrite <- CRmult_plus_distr_l. reflexivity.
Qed.

Lemma CRmin_plus : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    x + CRmin y z == CRmin (x + y) (x + z).
Proof.
  intros. unfold CRmin.
  unfold CRminus. setoid_replace (x + z + - (x + y)) with (z-y).
  - apply (CRmult_eq_reg_r (CR_of_Q _ 2)).
    + left. apply CR_of_Q_lt; reflexivity.
    + rewrite CRmult_plus_distr_r.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
      rewrite CRmult_1_r.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
      rewrite CRmult_1_r.
      rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
      do 3 rewrite (CRplus_assoc x). apply CRplus_morph.
      * reflexivity.
      * do 2 rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
        rewrite (CRplus_comm x). apply CRplus_assoc.
  - rewrite CRopp_plus_distr. rewrite <- CRplus_assoc.
    apply CRplus_morph. 2: reflexivity.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
    apply CRplus_0_l.
Qed.

Lemma CRmin_left : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x <= y -> CRmin x y == x.
Proof.
  intros. unfold CRmin.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  - left. apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
    rewrite CRabs_right.
    + unfold CRminus. rewrite CRopp_plus_distr.
      rewrite CRplus_assoc. apply CRplus_morph.
      * reflexivity.
      * rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l. apply CRopp_involutive.
    + rewrite <- (CRplus_opp_r x). apply CRplus_le_compat.
      * exact H.
      * apply CRle_refl.
Qed.

Lemma CRmin_right : forall {R : ConstructiveReals} (x y : CRcarrier R),
    y <= x -> CRmin x y == y.
Proof.
  intros. unfold CRmin.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  - left. apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
    rewrite CRabs_left.
    + unfold CRminus. do 2 rewrite CRopp_plus_distr.
      rewrite (CRplus_comm x y).
      rewrite CRplus_assoc. apply CRplus_morph.
      * reflexivity.
      * do 2 rewrite CRopp_involutive.
        rewrite CRplus_comm, CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
    + rewrite <- (CRplus_opp_r x). apply CRplus_le_compat.
      * exact H.
      * apply CRle_refl.
Qed.

Lemma CRmin_lt : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    z < x -> z < y -> z < CRmin x y.
Proof.
  intros. unfold CRmin.
  apply (CRmult_lt_reg_r (CR_of_Q R 2)).
  - apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    apply (CRplus_lt_reg_l _ (CRabs _ (y - x) - (z*CR_of_Q R 2))).
    unfold CRminus. rewrite CRplus_assoc. rewrite CRplus_opp_l, CRplus_0_r.
    rewrite (CRplus_comm (CRabs R (y + - x))).
    rewrite (CRplus_comm (x+y)), CRplus_assoc.
    rewrite <- (CRplus_assoc (CRabs R (y + - x))), CRplus_opp_r, CRplus_0_l.
    rewrite <- (CRplus_comm (x+y)).
    apply CRabs_def1.
    + unfold CRminus. rewrite <- (CRplus_comm y), CRplus_assoc.
      apply CRplus_lt_compat_l.
      apply (CRplus_lt_reg_l R (-x)).
      rewrite CRopp_mult_distr_l.
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite (CR_of_Q_plus R 1 1), CRmult_plus_distr_l.
      rewrite CRmult_1_r. apply CRplus_le_lt_compat.
      * apply CRlt_asym.
        apply CRopp_gt_lt_contravar, H.
      * apply CRopp_gt_lt_contravar, H.
    + rewrite CRopp_plus_distr, CRopp_involutive.
      rewrite CRplus_comm, CRplus_assoc.
      apply CRplus_lt_compat_l.
      apply (CRplus_lt_reg_l R (-y)).
      rewrite CRopp_mult_distr_l.
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite (CR_of_Q_plus R 1 1), CRmult_plus_distr_l.
      rewrite CRmult_1_r. apply CRplus_le_lt_compat.
      * apply CRlt_asym.
        apply CRopp_gt_lt_contravar, H0.
      * apply CRopp_gt_lt_contravar, H0.
Qed.

Lemma CRmin_contract : forall {R : ConstructiveReals} (x y a : CRcarrier R),
    CRabs _ (CRmin x a - CRmin y a) <= CRabs _ (x - y).
Proof.
  intros. unfold CRmin.
  unfold CRminus. rewrite CRopp_mult_distr_l, <- CRmult_plus_distr_r.
  rewrite (CRabs_morph
             _ ((x - y + (CRabs _ (a - y) - CRabs _ (a - x))) * CR_of_Q R (1 # 2))).
  - rewrite CRabs_mult, (CRabs_right (CR_of_Q R (1 # 2))).
    2: apply CR_of_Q_le; discriminate.
    apply (CRle_trans _
                      ((CRabs _ (x - y) * 1 + CRabs _ (x-y) * 1)
                       * CR_of_Q R (1 # 2))).
    + apply CRmult_le_compat_r.
      * apply CR_of_Q_le. discriminate.
      * apply (CRle_trans
                 _ (CRabs _ (x - y) + CRabs _ (CRabs _ (a - y) - CRabs _ (a - x)))).
        -- apply CRabs_triang.
        -- rewrite CRmult_1_r. apply CRplus_le_compat_l.
           rewrite (CRabs_morph (x-y) ((a-y)-(a-x))).
           ++ apply CRabs_triang_inv2.
           ++ unfold CRminus. rewrite (CRplus_comm (a + - y)).
              rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
              rewrite CRplus_comm, CRopp_plus_distr, <- CRplus_assoc.
              rewrite CRplus_opp_r, CRopp_involutive, CRplus_0_l.
              reflexivity.
    + rewrite <- CRmult_plus_distr_l.
      rewrite <- (CR_of_Q_plus R 1 1).
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 + 1) * (1 # 2))%Q with 1%Q. 2: reflexivity.
      rewrite CRmult_1_r. apply CRle_refl.
  - unfold CRminus. apply CRmult_morph. 2: reflexivity.
    do 4 rewrite CRplus_assoc. apply CRplus_morph.
    + reflexivity.
    + rewrite <- CRplus_assoc. rewrite CRplus_comm, CRopp_plus_distr.
      rewrite CRplus_assoc. apply CRplus_morph.
      * reflexivity.
      * rewrite CRopp_plus_distr. rewrite (CRplus_comm (-a)).
        rewrite CRplus_assoc, <- (CRplus_assoc (-a)), CRplus_opp_l.
        rewrite CRplus_0_l, CRopp_involutive. reflexivity.
Qed.

Lemma CRmin_glb : forall {R : ConstructiveReals} (x y z:CRcarrier R),
    z <= x -> z <= y -> z <= CRmin x y.
Proof.
  intros. unfold CRmin.
  apply (CRmult_le_reg_r (CR_of_Q R 2)).
  - apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    apply (CRplus_le_reg_l (CRabs _ (y-x) - (z*CR_of_Q R 2))).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite (CRplus_comm (CRabs R (y + - x) + - (z * CR_of_Q R 2))).
    rewrite CRplus_assoc, <- (CRplus_assoc (- CRabs R (y + - x))).
    rewrite CRplus_opp_l, CRplus_0_l.
    apply CRabs_le. split.
    + do 2 rewrite CRopp_plus_distr.
      rewrite CRopp_involutive, (CRplus_comm y), CRplus_assoc.
      apply CRplus_le_compat_l, (CRplus_le_reg_l y).
      rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
      rewrite (CR_of_Q_plus R 1 1), CRmult_plus_distr_l.
      rewrite CRmult_1_r. apply CRplus_le_compat; exact H0.
    + rewrite (CRplus_comm x), CRplus_assoc. apply CRplus_le_compat_l.
      apply (CRplus_le_reg_l (-x)).
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite CRopp_mult_distr_l.
      rewrite (CR_of_Q_plus R 1 1), CRmult_plus_distr_l.
      rewrite CRmult_1_r.
      apply CRplus_le_compat; apply CRopp_ge_le_contravar; exact H.
Qed.

Lemma CRmin_assoc : forall {R : ConstructiveReals} (a b c : CRcarrier R),
    CRmin a (CRmin b c) == CRmin (CRmin a b) c.
Proof.
  split.
  - apply CRmin_glb.
    + apply (CRle_trans _ (CRmin a b)).
      * apply CRmin_l. * apply CRmin_l.
    + apply CRmin_glb.
      * apply (CRle_trans _ (CRmin a b)).
        -- apply CRmin_l. -- apply CRmin_r.
      * apply CRmin_r.
  - apply CRmin_glb.
    + apply CRmin_glb.
      * apply CRmin_l.
      * apply (CRle_trans _ (CRmin b c)).
        -- apply CRmin_r.  -- apply CRmin_l.
    + apply (CRle_trans _ (CRmin b c)).
      * apply CRmin_r. * apply CRmin_r.
Qed.

Lemma CRlt_min : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    z < CRmin x y -> prod (z < x) (z < y).
Proof.
  intros. destruct (CR_Q_dense R _ _ H) as [q qmaj].
  destruct qmaj.
  split.
  - apply (CRlt_le_trans _ (CR_of_Q R q) _ c).
    intro abs. apply (CRlt_asym _ _ c0).
    apply (CRle_lt_trans _ x).
    + apply CRmin_l.
    + exact abs.
  - apply (CRlt_le_trans _ (CR_of_Q R q) _ c).
    intro abs. apply (CRlt_asym _ _ c0).
    apply (CRle_lt_trans _ y).
    + apply CRmin_r.
    + exact abs.
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

#[global]
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
  apply (CRmult_le_reg_r (CR_of_Q _ 2)).
  - apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    apply (CRplus_le_reg_l (-x-y)).
    rewrite <- CRplus_assoc. unfold CRminus.
    rewrite <- CRopp_plus_distr, CRplus_opp_l, CRplus_0_l.
    apply CRabs_le. split.
    + repeat rewrite CRopp_plus_distr.
      do 2 rewrite CRopp_involutive.
      rewrite (CRplus_comm x), CRplus_assoc. apply CRplus_le_compat_l.
      apply (CRplus_le_reg_l (-x)).
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
      rewrite CRopp_plus_distr.
      apply CRplus_le_compat; apply CRopp_ge_le_contravar; assumption.
    + rewrite (CRplus_comm y), CRopp_plus_distr, CRplus_assoc.
      apply CRplus_le_compat_l.
      apply (CRplus_le_reg_l y).
      rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
      rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
      apply CRplus_le_compat; assumption.
Qed.

Lemma CRmax_l : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x <= CRmax x y.
Proof.
  intros. unfold CRmax.
  apply (CRmult_le_reg_r (CR_of_Q R 2)).
  - apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    setoid_replace 2%Q with (1+1)%Q.
    + rewrite CR_of_Q_plus.
      rewrite CRmult_plus_distr_l, CRmult_1_r, CRplus_assoc.
      apply CRplus_le_compat_l.
      apply (CRplus_le_reg_l (-y)).
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite CRabs_minus_sym, CRplus_comm.
      apply CRle_abs.
    + reflexivity.
Qed.

Lemma CRmax_r : forall {R : ConstructiveReals} (x y : CRcarrier R),
    y <= CRmax x y.
Proof.
  intros. unfold CRmax.
  apply (CRmult_le_reg_r (CR_of_Q _ 2)).
  - apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
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
  - apply (CRmult_eq_reg_r (CR_of_Q _ 2)).
    + left. apply CR_of_Q_lt; reflexivity.
    + rewrite CRmult_plus_distr_r.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
      rewrite CRmult_1_r.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
      rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
      rewrite CRmult_1_r.
      do 3 rewrite (CRplus_assoc x). apply CRplus_morph.
      * reflexivity.
      * do 2 rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
        rewrite (CRplus_comm x). apply CRplus_assoc.
  - unfold CRminus. rewrite CRopp_plus_distr. rewrite <- CRplus_assoc.
    apply CRplus_morph. 2: reflexivity.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
    apply CRplus_0_l.
Qed.

Lemma CRmax_left : forall {R : ConstructiveReals} (x y : CRcarrier R),
    y <= x -> CRmax x y == x.
Proof.
  intros. unfold CRmax.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  - left. apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
    rewrite CRplus_assoc. apply CRplus_morph.
    + reflexivity.
    + rewrite CRabs_left.
      * unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive.
        rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l. reflexivity.
      * rewrite <- (CRplus_opp_r x). apply CRplus_le_compat_r. exact H.
Qed.

Lemma CRmax_right : forall {R : ConstructiveReals} (x y : CRcarrier R),
    x <= y -> CRmax x y == y.
Proof.
  intros. unfold CRmax.
  apply (CRmult_eq_reg_r (CR_of_Q R 2)).
  - left. apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    rewrite (CR_of_Q_plus _ 1 1), CRmult_plus_distr_l, CRmult_1_r.
    rewrite (CRplus_comm x y).
    rewrite CRplus_assoc. apply CRplus_morph.
    + reflexivity.
    + rewrite CRabs_right.
      * unfold CRminus. rewrite CRplus_comm.
        rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
      * rewrite <- (CRplus_opp_r x). apply CRplus_le_compat_r. exact H.
Qed.

Lemma CRmax_contract : forall {R : ConstructiveReals} (x y a : CRcarrier R),
    CRabs _ (CRmax x a - CRmax y a) <= CRabs _ (x - y).
Proof.
  intros. unfold CRmax.
  rewrite (CRabs_morph
             _ ((x - y + (CRabs _ (a - x) - CRabs _ (a - y))) * CR_of_Q R (1 # 2))).
  - rewrite CRabs_mult, (CRabs_right (CR_of_Q R (1 # 2))).
    2: apply CR_of_Q_le; discriminate.
    apply (CRle_trans
             _ ((CRabs _ (x - y) * 1 + CRabs _ (x-y) * 1)
                * CR_of_Q R (1 # 2))).
    + apply CRmult_le_compat_r.
      * apply CR_of_Q_le. discriminate.
      * apply (CRle_trans
                 _ (CRabs _ (x - y) + CRabs _ (CRabs _ (a - x) - CRabs _ (a - y)))).
        -- apply CRabs_triang.
        -- rewrite CRmult_1_r. apply CRplus_le_compat_l.
           rewrite (CRabs_minus_sym x y).
           rewrite (CRabs_morph (y-x) ((a-x)-(a-y))).
           ++ apply CRabs_triang_inv2.
           ++ unfold CRminus. rewrite (CRplus_comm (a + - x)).
              rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
              rewrite CRplus_comm, CRopp_plus_distr, <- CRplus_assoc.
              rewrite CRplus_opp_r, CRopp_involutive, CRplus_0_l.
              reflexivity.
    + rewrite <- CRmult_plus_distr_l.
      rewrite <- (CR_of_Q_plus R 1 1).
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 + 1) * (1 # 2))%Q with 1%Q. 2: reflexivity.
      rewrite CRmult_1_r. apply CRle_refl.
  - unfold CRminus. rewrite CRopp_mult_distr_l.
    rewrite <- CRmult_plus_distr_r. apply CRmult_morph. 2: reflexivity.
    do 4 rewrite CRplus_assoc. apply CRplus_morph.
    + reflexivity.
    + rewrite <- CRplus_assoc. rewrite CRplus_comm, CRopp_plus_distr.
      rewrite CRplus_assoc. apply CRplus_morph.
      * reflexivity.
      * rewrite CRopp_plus_distr. rewrite (CRplus_comm (-a)).
        rewrite CRplus_assoc, <- (CRplus_assoc (-a)), CRplus_opp_l.
        rewrite CRplus_0_l. apply CRplus_comm.
Qed.

Lemma CRmax_lub_lt : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    x < z -> y < z -> CRmax x y < z.
Proof.
  intros. unfold CRmax.
  apply (CRmult_lt_reg_r (CR_of_Q R 2)).
  - apply CR_of_Q_lt; reflexivity.
  - rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CRmult_1_r.
    apply (CRplus_lt_reg_l _ (-y -x)). unfold CRminus.
    rewrite CRplus_assoc, <- (CRplus_assoc (-x)), <- (CRplus_assoc (-x)).
    rewrite CRplus_opp_l, CRplus_0_l, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    apply CRabs_def1.
    + rewrite (CRplus_comm y), (CRplus_comm (-y)), CRplus_assoc.
      apply CRplus_lt_compat_l.
      apply (CRplus_lt_reg_l _ y).
      rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
      rewrite (CR_of_Q_plus R 1 1), CRmult_plus_distr_l.
      rewrite CRmult_1_r. apply CRplus_le_lt_compat.
      * apply CRlt_asym, H0.
      * exact H0.
    + rewrite CRopp_plus_distr, CRopp_involutive.
      rewrite CRplus_assoc. apply CRplus_lt_compat_l.
      apply (CRplus_lt_reg_l _ x).
      rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
      rewrite (CR_of_Q_plus R 1 1), CRmult_plus_distr_l.
      rewrite CRmult_1_r. apply CRplus_le_lt_compat.
      * apply CRlt_asym, H.
      * exact H.
Qed.

Lemma CRmax_assoc : forall {R : ConstructiveReals} (a b c : CRcarrier R),
    CRmax a (CRmax b c) == CRmax (CRmax a b) c.
Proof.
  split.
  - apply CRmax_lub.
    + apply CRmax_lub.
      * apply CRmax_l.
      * apply (CRle_trans _ (CRmax b c)).
        -- apply CRmax_l.
        -- apply CRmax_r.
    + apply (CRle_trans _ (CRmax b c)).
      * apply CRmax_r.
      * apply CRmax_r.
  - apply CRmax_lub.
    + apply (CRle_trans _ (CRmax a b)).
      * apply CRmax_l.
      * apply CRmax_l.
    + apply CRmax_lub.
      * apply (CRle_trans _ (CRmax a b)).
        -- apply CRmax_r.
        -- apply CRmax_l.
      * apply CRmax_r.
Qed.

Lemma CRmax_min_mult_neg :
  forall {R : ConstructiveReals} (p q r:CRcarrier R),
    r <= 0 -> CRmax (r * p) (r * q) == r * CRmin p q.
Proof.
  intros R p q r H. unfold CRmin, CRmax.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  - rewrite CRabs_mult.
    rewrite (CRabs_left r), <- CRmult_assoc.
    + apply CRmult_morph. 2: reflexivity. unfold CRminus.
      rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r,
        CRmult_plus_distr_l, CRmult_plus_distr_l.
      reflexivity.
    + exact H.
  - unfold CRminus. rewrite CRmult_plus_distr_l, CRopp_mult_distr_r. reflexivity.
Qed.

Lemma CRlt_max : forall {R : ConstructiveReals} (x y z : CRcarrier R),
    CRmax x y < z -> prod (x < z) (y < z).
Proof.
  intros. destruct (CR_Q_dense R _ _ H) as [q qmaj].
  destruct qmaj.
  split.
  - apply (CRlt_le_trans _ (CR_of_Q R q)).
    + apply (CRle_lt_trans _ (CRmax x y)).
      * apply CRmax_l.
      * exact c.
    + apply CRlt_asym, c0.
  - apply (CRlt_le_trans _ (CR_of_Q R q)).
    + apply (CRle_lt_trans _ (CRmax x y)).
      * apply CRmax_r.
      * exact c.
    + apply CRlt_asym, c0.
Qed.

Lemma CRmax_mult :
  forall {R : ConstructiveReals} (p q r:CRcarrier R),
    0 <= r -> CRmax (r * p) (r * q) == r * CRmax p q.
Proof.
  intros R p q r H. unfold CRmin, CRmax.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  - rewrite CRabs_mult.
    rewrite (CRabs_right r), <- CRmult_assoc.
    + apply CRmult_morph. 2: reflexivity.
      rewrite CRmult_plus_distr_l, CRmult_plus_distr_l.
      reflexivity.
    + exact H.
  - unfold CRminus. rewrite CRmult_plus_distr_l, CRopp_mult_distr_r. reflexivity.
Qed.

Lemma CRmin_max_mult_neg :
  forall {R : ConstructiveReals} (p q r:CRcarrier R),
    r <= 0 -> CRmin (r * p) (r * q) == r * CRmax p q.
Proof.
  intros R p q r H. unfold CRmin, CRmax.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  - rewrite CRabs_mult.
    rewrite (CRabs_left r), <- CRmult_assoc.
    + apply CRmult_morph. 2: reflexivity. unfold CRminus.
      rewrite CRopp_mult_distr_l, CRopp_involutive,
        CRmult_plus_distr_l, CRmult_plus_distr_l.
      reflexivity.
    + exact H.
  - unfold CRminus. rewrite CRmult_plus_distr_l, CRopp_mult_distr_r. reflexivity.
Qed.

Lemma CRmorph_min : forall {R1 R2 : ConstructiveReals}
                      (f : @ConstructiveRealsMorphism R1 R2)
                      (a b : CRcarrier R1),
    CRmorph f (CRmin a b)
    == CRmin (CRmorph f a) (CRmorph f b).
Proof.
  intros. unfold CRmin.
  rewrite CRmorph_mult. apply CRmult_morph.
  2: apply CRmorph_rat.
  unfold CRminus. do 2 rewrite CRmorph_plus. apply CRplus_morph.
  - apply CRplus_morph.
    + reflexivity.
    + reflexivity.
  - rewrite CRmorph_opp. apply CRopp_morph.
    rewrite <- CRmorph_abs. apply CRabs_morph.
    rewrite CRmorph_plus. apply CRplus_morph.
    + reflexivity.
    + rewrite CRmorph_opp. apply CRopp_morph, CRmorph_proper. reflexivity.
Qed.
