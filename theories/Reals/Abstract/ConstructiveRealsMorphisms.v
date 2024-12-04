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

(** Morphisms used to transport results from any instance of
    ConstructiveReals to any other.
    Between any two constructive reals structures R1 and R2,
    all morphisms R1 -> R2 are extensionally equal. We will
    further show that they exist, and so are isomorphisms.
    The difference between two morphisms R1 -> R2 is therefore
    the speed of computation.

    The canonical isomorphisms we provide here are often very slow,
    when a new implementation of constructive reals is added,
    it should define its own ad hoc isomorphisms for better speed.

    Apart from the speed, those unique isomorphisms also serve as
    sanity checks of the interface ConstructiveReals :
    it captures a concept with a strong notion of uniqueness.

    WARNING: this file is experimental and likely to change in future releases.
*)

Require Import QArith.
Require Import Qabs.
Require Import Znat.
Require Import ConstructiveReals.
Require Import ConstructiveLimits.
Require Import ConstructiveAbs.

Local Open Scope ConstructiveReals.

Record ConstructiveRealsMorphism {R1 R2 : ConstructiveReals} : Set :=
  {
    CRmorph : CRcarrier R1 -> CRcarrier R2;
    CRmorph_rat : forall q : Q,
        CRmorph (CR_of_Q R1 q) == CR_of_Q R2 q;
    CRmorph_increasing : forall x y : CRcarrier R1,
        CRlt R1 x y -> CRlt R2 (CRmorph x) (CRmorph y);
  }.


Lemma CRmorph_increasing_inv
  : forall {R1 R2 : ConstructiveReals}
      (f : ConstructiveRealsMorphism)
      (x y : CRcarrier R1),
    CRlt R2 (CRmorph f x) (CRmorph f y)
    -> CRlt R1 x y.
Proof.
  intros. destruct (CR_Q_dense R2 _ _ H) as [q [H0 H1]].
  destruct (CR_Q_dense R2 _ _ H0) as [r [H2 H3]].
  apply lt_CR_of_Q, (CR_of_Q_lt R1) in H3.
  destruct (CRltLinear R1).
  destruct (s _ x _ H3).
  - exfalso. apply (CRmorph_increasing f) in c.
    destruct (CRmorph_rat f r) as [H4 _].
    apply (CRle_lt_trans _ _ _ H4) in c. clear H4.
    exact (CRlt_asym _ _ c H2).
  - clear H2 H3 r. apply (CRlt_trans _ _ _ c). clear c.
    destruct (CR_Q_dense R2 _ _ H1) as [t [H2 H3]].
    apply lt_CR_of_Q, (CR_of_Q_lt R1) in H2.
    destruct (s _ y _ H2). { exact c. }
    exfalso. apply (CRmorph_increasing f) in c.
    destruct (CRmorph_rat f t) as [_ H4].
    apply (CRlt_le_trans _ _ _ c) in H4. clear c.
    exact (CRlt_asym _ _ H4 H3).
Qed.

Lemma CRmorph_unique : forall {R1 R2 : ConstructiveReals}
                         (f g : @ConstructiveRealsMorphism R1 R2)
                         (x : CRcarrier R1),
    CRmorph f x == CRmorph g x.
Proof.
  split.
  - intro abs. destruct (CR_Q_dense R2 _ _ abs) as [q [H H0]].
    destruct (CRmorph_rat f q) as [H1 _].
    apply (CRlt_le_trans _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    destruct (CRmorph_rat g q) as [_ H2].
    apply (CRle_lt_trans _ _ _ H2) in H0. clear H2.
    apply CRmorph_increasing_inv in H0.
    exact (CRlt_asym _ _ H0 H1).
  - intro abs. destruct (CR_Q_dense R2 _ _ abs) as [q [H H0]].
    destruct (CRmorph_rat f q) as [_ H1].
    apply (CRle_lt_trans _ _ _ H1) in H0. clear H1.
    apply CRmorph_increasing_inv in H0.
    destruct (CRmorph_rat g q) as [H2 _].
    apply (CRlt_le_trans _ _ _ H) in H2. clear H.
    apply CRmorph_increasing_inv in H2.
    exact (CRlt_asym _ _ H0 H2).
Qed.


(* The identity is the only endomorphism of constructive reals.
   For any ConstructiveReals R1, R2 and any morphisms
   f : R1 -> R2 and g : R2 -> R1,
   f and g are isomorphisms and are inverses of each other. *)
Lemma Endomorph_id
  : forall {R : ConstructiveReals} (f : @ConstructiveRealsMorphism R R)
      (x : CRcarrier R),
    CRmorph f x == x.
Proof.
  split.
  - intro abs. destruct (CR_Q_dense R _ _ abs) as [q [H0 H1]].
    destruct (CRmorph_rat f q) as [H _].
    apply (CRlt_le_trans _ _ _ H0) in H. clear H0.
    apply CRmorph_increasing_inv in H.
    exact (CRlt_asym _ _ H1 H).
  - intro abs. destruct (CR_Q_dense R _ _ abs) as [q [H0 H1]].
    destruct (CRmorph_rat f q) as [_ H].
    apply (CRle_lt_trans _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    exact (CRlt_asym _ _ H1 H0).
Qed.

Lemma CRmorph_proper
  : forall {R1 R2 : ConstructiveReals}
      (f : @ConstructiveRealsMorphism R1 R2)
      (x y : CRcarrier R1),
    x == y -> CRmorph f x == CRmorph f y.
Proof.
  split.
  - intro abs. apply CRmorph_increasing_inv in abs.
    destruct H. contradiction.
  - intro abs. apply CRmorph_increasing_inv in abs.
    destruct H. contradiction.
Qed.

Definition CRmorph_compose {R1 R2 R3 : ConstructiveReals}
           (f : @ConstructiveRealsMorphism R1 R2)
           (g : @ConstructiveRealsMorphism R2 R3)
  : @ConstructiveRealsMorphism R1 R3.
Proof.
  apply (Build_ConstructiveRealsMorphism
           R1 R3 (fun x:CRcarrier R1 => CRmorph g (CRmorph f x))).
  - intro q. apply (CReq_trans _ (CRmorph g (CR_of_Q R2 q))).
    + apply CRmorph_proper. apply CRmorph_rat.
    + apply CRmorph_rat.
  - intros. apply CRmorph_increasing. apply CRmorph_increasing. exact H.
Defined.

Lemma CRmorph_le : forall {R1 R2 : ConstructiveReals}
                     (f : @ConstructiveRealsMorphism R1 R2)
                     (x y : CRcarrier R1),
    x <= y -> CRmorph f x <= CRmorph f y.
Proof.
  intros. intro abs. apply CRmorph_increasing_inv in abs. contradiction.
Qed.

Lemma CRmorph_le_inv : forall {R1 R2 : ConstructiveReals}
                         (f : @ConstructiveRealsMorphism R1 R2)
                         (x y : CRcarrier R1),
    CRmorph f x <= CRmorph f y -> x <= y.
Proof.
  intros. intro abs. apply (CRmorph_increasing f) in abs. contradiction.
Qed.

Lemma CRmorph_zero : forall {R1 R2 : ConstructiveReals}
                       (f : @ConstructiveRealsMorphism R1 R2),
    CRmorph f 0 == 0.
Proof.
  intros. apply (CReq_trans _ (CRmorph f (CR_of_Q R1 0))).
  - apply CRmorph_proper. reflexivity.
  - apply CRmorph_rat.
Qed.

Lemma CRmorph_one : forall {R1 R2 : ConstructiveReals}
                      (f : @ConstructiveRealsMorphism R1 R2),
    CRmorph f 1 == 1.
Proof.
  intros. apply (CReq_trans _ (CRmorph f (CR_of_Q R1 1))).
  - apply CRmorph_proper. reflexivity.
  - apply CRmorph_rat.
Qed.

Lemma CRmorph_opp : forall {R1 R2 : ConstructiveReals}
                      (f : @ConstructiveRealsMorphism R1 R2)
                      (x : CRcarrier R1),
    CRmorph f (- x) == - CRmorph f x.
Proof.
  split.
  - intro abs.
    destruct (CR_Q_dense R2 _ _ abs) as [q [H H0]]. clear abs.
    destruct (CRmorph_rat f q) as [H1 _].
    apply (CRlt_le_trans _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    apply CRopp_gt_lt_contravar in H0.
    destruct (@CR_of_Q_opp R2 q) as [H2 _].
    apply (CRlt_le_trans _ _ _ H0) in H2. clear H0.
    pose proof (CRopp_involutive (CRmorph f x)) as [H _].
    apply (CRle_lt_trans _ _ _ H) in H2. clear H.
    destruct (CRmorph_rat f (-q)) as [H _].
    apply (CRlt_le_trans _ _ _ H2) in H. clear H2.
    apply CRmorph_increasing_inv in H.
    destruct (@CR_of_Q_opp R1 q) as [_ H2].
    apply (CRlt_le_trans _ _ _ H) in H2. clear H.
    apply CRopp_gt_lt_contravar in H2.
    pose proof (CRopp_involutive (CR_of_Q R1 q)) as [H _].
    apply (CRle_lt_trans _ _ _ H) in H2. clear H.
    exact (CRlt_asym _ _ H1 H2).
  - intro abs.
    destruct (CR_Q_dense R2 _ _ abs) as [q [H H0]]. clear abs.
    destruct (CRmorph_rat f q) as [_ H1].
    apply (CRle_lt_trans _ _ _ H1) in H0. clear H1.
    apply CRmorph_increasing_inv in H0.
    apply CRopp_gt_lt_contravar in H.
    pose proof (CRopp_involutive (CRmorph f x)) as [_ H1].
    apply (CRlt_le_trans _ _ _ H) in H1. clear H.
    destruct (@CR_of_Q_opp R2 q) as [_ H2].
    apply (CRle_lt_trans _ _ _ H2) in H1. clear H2.
    destruct (CRmorph_rat f (-q)) as [_ H].
    apply (CRle_lt_trans _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    destruct (@CR_of_Q_opp R1 q) as [H2 _].
    apply (CRle_lt_trans _ _ _ H2) in H1. clear H2.
    apply CRopp_gt_lt_contravar in H1.
    pose proof (CRopp_involutive (CR_of_Q R1 q)) as [_ H].
    apply (CRlt_le_trans _ _ _ H1) in H. clear H1.
    exact (CRlt_asym _ _ H0 H).
Qed.

Lemma CRplus_pos_rat_lt : forall {R : ConstructiveReals} (x : CRcarrier R) (q : Q),
    Qlt 0 q -> CRlt R x (CRplus R x (CR_of_Q R q)).
Proof.
  intros.
  apply (CRle_lt_trans _ (CRplus R x 0)).
  - apply CRplus_0_r.
  - apply CRplus_lt_compat_l.
    apply (CRle_lt_trans _ (CR_of_Q R 0)).
    + apply CRle_refl.
    + apply CR_of_Q_lt. exact H.
Qed.

Lemma CRplus_neg_rat_lt : forall {R : ConstructiveReals} (x : CRcarrier R) (q : Q),
    Qlt q 0 -> CRlt R (CRplus R x (CR_of_Q R q)) x.
Proof.
  intros.
  apply (CRlt_le_trans _ (CRplus R x 0)). 2: apply CRplus_0_r.
  apply CRplus_lt_compat_l.
  apply (CRlt_le_trans _ (CR_of_Q R 0)).
  - apply CR_of_Q_lt. exact H.
  - apply CRle_refl.
Qed.

Lemma CRmorph_plus_rat : forall {R1 R2 : ConstructiveReals}
                                (f : @ConstructiveRealsMorphism R1 R2)
                                (x : CRcarrier R1) (q : Q),
    CRmorph f (CRplus R1 x (CR_of_Q R1 q))
    == CRplus R2 (CRmorph f x) (CR_of_Q R2 q).
Proof.
  split.
  - intro abs.
    destruct (CR_Q_dense R2 _ _ abs) as [r [H H0]]. clear abs.
    destruct (CRmorph_rat f r) as [H1 _].
    apply (CRlt_le_trans _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    apply (CRlt_asym _ _ H1). clear H1.
    apply (CRplus_lt_reg_r (CRopp R1 (CR_of_Q R1 q))).
    apply (CRlt_le_trans _ x).
    + apply (CRle_lt_trans _ (CR_of_Q R1 (r-q))).
      * apply (CRle_trans _ (CRplus R1 (CR_of_Q R1 r) (CR_of_Q R1 (-q)))).
        -- apply CRplus_le_compat_l. destruct (@CR_of_Q_opp R1 q). exact H.
        -- destruct (CR_of_Q_plus R1 r (-q)). exact H.
      * apply (CRmorph_increasing_inv f).
        apply (CRle_lt_trans _ (CR_of_Q R2 (r - q))).
        -- apply CRmorph_rat.
        -- apply (CRplus_lt_reg_r (CR_of_Q R2 q)).
           apply (CRle_lt_trans _ (CR_of_Q R2 r)). 2: exact H0.
           intro H.
           destruct (CR_of_Q_plus R2 (r-q) q) as [H1 _].
           apply (CRlt_le_trans _ _ _ H) in H1. clear H.
           apply lt_CR_of_Q in H1. ring_simplify in H1.
           exact (Qlt_not_le _ _ H1 (Qle_refl _)).
    + destruct (CRisRing R1).
      apply (CRle_trans
               _ (CRplus R1 x (CRplus R1 (CR_of_Q R1 q) (CRopp R1 (CR_of_Q R1 q))))).
      * apply (CRle_trans _ (CRplus R1 x 0)).
        -- destruct (CRplus_0_r x). exact H.
        -- apply CRplus_le_compat_l. destruct (Ropp_def (CR_of_Q R1 q)). exact H.
      * destruct (Radd_assoc x (CR_of_Q R1 q) (CRopp R1 (CR_of_Q R1 q))).
        exact H1.
  - intro abs.
    destruct (CR_Q_dense R2 _ _ abs) as [r [H H0]]. clear abs.
    destruct (CRmorph_rat f r) as [_ H1].
    apply (CRle_lt_trans _ _ _ H1) in H0. clear H1.
    apply CRmorph_increasing_inv in H0.
    apply (CRlt_asym _ _ H0). clear H0.
    apply (CRplus_lt_reg_r (CRopp R1 (CR_of_Q R1 q))).
    apply (CRle_lt_trans _ x).
    + destruct (CRisRing R1).
      apply (CRle_trans
               _ (CRplus R1 x (CRplus R1 (CR_of_Q R1 q) (CRopp R1 (CR_of_Q R1 q))))).
      * destruct (Radd_assoc x (CR_of_Q R1 q) (CRopp R1 (CR_of_Q R1 q))).
        exact H0.
      * apply (CRle_trans _ (CRplus R1 x 0)).
        -- apply CRplus_le_compat_l. destruct (Ropp_def (CR_of_Q R1 q)). exact H1.
        -- destruct (CRplus_0_r x). exact H1.
    + apply (CRlt_le_trans _ (CR_of_Q R1 (r-q))).
      * apply (CRmorph_increasing_inv f).
        apply (CRlt_le_trans _ (CR_of_Q R2 (r - q))).
        2: apply CRmorph_rat.
        apply (CRplus_lt_reg_r (CR_of_Q R2 q)).
        apply (CRlt_le_trans _ _ _ H).
        apply (CRle_trans _ (CR_of_Q R2 (r-q+q))).
        -- intro abs. apply lt_CR_of_Q in abs. ring_simplify in abs.
           exact (Qlt_not_le _ _ abs (Qle_refl _)).
        -- destruct (CR_of_Q_plus R2 (r-q) q). exact H1.
      * apply (CRle_trans _ (CRplus R1 (CR_of_Q R1 r) (CR_of_Q R1 (-q)))).
        -- destruct (CR_of_Q_plus R1 r (-q)). exact H1.
        -- apply CRplus_le_compat_l. destruct (@CR_of_Q_opp R1 q). exact H1.
Qed.

Lemma CRmorph_plus : forall {R1 R2 : ConstructiveReals}
                       (f : @ConstructiveRealsMorphism R1 R2)
                       (x y : CRcarrier R1),
    CRmorph f (CRplus R1 x y)
    == CRplus R2 (CRmorph f x) (CRmorph f y).
Proof.
  intros R1 R2 f.
  assert (forall (x y : CRcarrier R1),
             CRplus R2 (CRmorph f x) (CRmorph f y)
             <= CRmorph f (CRplus R1 x y)).
  { intros x y abs. destruct (CR_Q_dense R2 _ _ abs) as [r [H H0]]. clear abs.
    destruct (CRmorph_rat f r) as [H1 _].
    apply (CRlt_le_trans _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    apply (CRlt_asym _ _ H1). clear H1.
    destruct (CR_Q_dense R2 _ _ H0) as [q [H2 H3]].
    apply lt_CR_of_Q in H2.
    assert (Qlt (r-q) 0) as epsNeg.
    { apply (Qplus_lt_r _ _ q). ring_simplify. exact H2. }
    destruct (CR_Q_dense R1 _ _ (CRplus_neg_rat_lt x (r-q) epsNeg))
      as [s [H4 H5]].
    apply (CRlt_trans _ (CRplus R1 (CR_of_Q R1 s) y)).
    2: apply CRplus_lt_compat_r, H5.
    apply (CRmorph_increasing_inv f).
    apply (CRlt_le_trans _ (CRplus R2 (CR_of_Q R2 s) (CRmorph f y))).
    - apply (CRmorph_increasing f) in H4.
      destruct (CRmorph_plus_rat f x (r-q)) as [H _].
      apply (CRle_lt_trans _ _ _ H) in H4. clear H.
      destruct (CRmorph_rat f s) as [_ H1].
      apply (CRlt_le_trans _ _ _ H4) in H1. clear H4.
      apply (CRlt_trans
               _ (CRplus R2 (CRplus R2 (CRmorph f x) (CR_of_Q R2 (r - q)))
                         (CRmorph f y))).
      2: apply CRplus_lt_compat_r, H1.
      apply (CRlt_le_trans
               _ (CRplus R2 (CRplus R2 (CR_of_Q R2 (r - q)) (CRmorph f x))
                         (CRmorph f y))).
      + apply (CRlt_le_trans
                 _ (CRplus R2 (CR_of_Q R2 (r - q))
                           (CRplus R2 (CRmorph f x) (CRmorph f y)))).
        * apply (CRle_lt_trans _ (CRplus R2 (CR_of_Q R2 (r - q)) (CR_of_Q R2 q))).
          2: apply CRplus_lt_compat_l, H3.
          intro abs.
          destruct (CR_of_Q_plus R2 (r-q) q) as [_ H4].
          apply (CRle_lt_trans _ _ _ H4) in abs. clear H4.
          destruct (CRmorph_rat f r) as [_ H4].
          apply (CRlt_le_trans _ _ _ abs) in H4. clear abs.
          apply lt_CR_of_Q in H4. ring_simplify in H4.
          exact (Qlt_not_le _ _ H4 (Qle_refl _)).
        * destruct (CRisRing R2); apply Radd_assoc.
      + apply CRplus_le_compat_r. destruct (CRisRing R2).
        destruct (Radd_comm (CRmorph f x) (CR_of_Q R2 (r - q))).
        exact H.
    - intro abs.
      destruct (CRmorph_plus_rat f y s) as [H _]. apply H. clear H.
      apply (CRlt_le_trans _ (CRplus R2 (CR_of_Q R2 s) (CRmorph f y))).
      + apply (CRle_lt_trans _ (CRmorph f (CRplus R1 (CR_of_Q R1 s) y))).
        * apply CRmorph_proper. destruct (CRisRing R1); apply Radd_comm.
        * exact abs.
      + destruct (CRisRing R2); apply Radd_comm. }
  split.
  - apply H.
  - specialize (H (CRplus R1 x y) (CRopp R1 y)).
    intro abs. apply H. clear H.
    apply (CRle_lt_trans _ (CRmorph f x)).
    + apply CRmorph_proper. destruct (CRisRing R1).
      apply (CReq_trans _ (CRplus R1 x (CRplus R1 y (CRopp R1 y)))).
      * apply CReq_sym, Radd_assoc.
      * apply (CReq_trans _ (CRplus R1 x 0)). 2: apply CRplus_0_r.
        destruct (CRisRingExt R1). apply Radd_ext.
        -- apply CReq_refl.
        -- apply Ropp_def.
    + apply (CRplus_lt_reg_r (CRmorph f y)).
      apply (CRlt_le_trans _ _ _ abs). clear abs.
      apply (CRle_trans _ (CRplus R2 (CRmorph f (CRplus R1 x y)) 0)).
      * destruct (CRplus_0_r (CRmorph f (CRplus R1 x y))). exact H.
      * apply (CRle_trans _ (CRplus R2 (CRmorph f (CRplus R1 x y))
                                    (CRplus R2 (CRmorph f (CRopp R1 y)) (CRmorph f y)))).
        -- apply CRplus_le_compat_l.
           apply (CRle_trans
                    _ (CRplus R2 (CRopp R2 (CRmorph f y)) (CRmorph f y))).
           ++ destruct (CRplus_opp_l (CRmorph f y)). exact H.
           ++ apply CRplus_le_compat_r. destruct (CRmorph_opp f y). exact H.
        -- destruct (CRisRing R2).
           destruct (Radd_assoc (CRmorph f (CRplus R1 x y))
                                (CRmorph f (CRopp R1 y)) (CRmorph f y)).
           exact H0.
Qed.

Lemma CRmorph_mult_pos : forall {R1 R2 : ConstructiveReals}
                           (f : @ConstructiveRealsMorphism R1 R2)
                           (x : CRcarrier R1) (n : nat),
    CRmorph f (CRmult R1 x (CR_of_Q R1 (Z.of_nat n # 1)))
    == CRmult R2 (CRmorph f x) (CR_of_Q R2 (Z.of_nat n # 1)).
Proof.
  induction n.
  - simpl. destruct (CRisRingExt R1).
    apply (CReq_trans _ 0).
    + apply (CReq_trans _ (CRmorph f 0)).
      2: apply CRmorph_zero. apply CRmorph_proper.
      apply (CReq_trans _ (CRmult R1 x 0)).
      2: apply CRmult_0_r. apply Rmul_ext. * apply CReq_refl. * reflexivity.
    + apply (CReq_trans _ (CRmult R2 (CRmorph f x) 0)).
      * apply CReq_sym, CRmult_0_r.
      * destruct (CRisRingExt R2).
        apply Rmul_ext0.
        -- apply CReq_refl.
        -- reflexivity.
   - destruct (CRisRingExt R1), (CRisRingExt R2).
    transitivity (CRmorph f (CRplus R1 x (CRmult R1 x (CR_of_Q R1 (Z.of_nat n # 1))))).
     + apply CRmorph_proper.
       transitivity (CRmult R1 x (CRplus R1 1 (CR_of_Q R1 (Z.of_nat n # 1)))).
       * apply Rmul_ext.
         -- reflexivity.
         -- transitivity (CR_of_Q R1 (1 + (Z.of_nat n # 1))).
            ++ apply CR_of_Q_morph. rewrite Nat2Z.inj_succ. unfold Z.succ.
               rewrite Z.add_comm. rewrite Qinv_plus_distr. reflexivity.
            ++ rewrite CR_of_Q_plus. reflexivity.
       * transitivity (CRplus R1 (CRmult R1 x 1)
                              (CRmult R1 x (CR_of_Q R1 (Z.of_nat n # 1)))).
         -- apply CRmult_plus_distr_l.
         -- apply Radd_ext.
            ++ apply CRmult_1_r.
            ++ reflexivity.
     + apply (CReq_trans
                _ (CRplus R2 (CRmorph f x)
                          (CRmorph f (CRmult R1 x (CR_of_Q R1 (Z.of_nat n # 1)))))).
       * apply CRmorph_plus.
       * apply (CReq_trans
                  _ (CRplus R2 (CRmorph f x)
                            (CRmult R2 (CRmorph f x) (CR_of_Q R2 (Z.of_nat n # 1))))).
         -- apply Radd_ext0.
            ++ apply CReq_refl.
            ++ exact IHn.
         -- apply (CReq_trans
                     _ (CRmult R2 (CRmorph f x) (CRplus R2 1 (CR_of_Q R2 (Z.of_nat n # 1))))).
            1:apply (CReq_trans
                        _ (CRplus R2 (CRmult R2 (CRmorph f x) 1)
                                  (CRmult R2 (CRmorph f x) (CR_of_Q R2 (Z.of_nat n # 1))))).
            ++ apply Radd_ext0. 2: apply CReq_refl. apply CReq_sym, CRmult_1_r.
            ++ apply CReq_sym, CRmult_plus_distr_l.
            ++ apply Rmul_ext0.
               ** apply CReq_refl.
               ** apply (CReq_trans _ (CR_of_Q R2 (1 + (Z.of_nat n # 1)))).
                  1:apply (CReq_trans _ (CRplus R2 (CR_of_Q R2 1) (CR_of_Q R2 (Z.of_nat n # 1)))).
                  { apply Radd_ext0; reflexivity. }
                  { apply CReq_sym, CR_of_Q_plus. }
                  apply CR_of_Q_morph. rewrite Nat2Z.inj_succ. unfold Z.succ.
                  rewrite Z.add_comm. rewrite Qinv_plus_distr. reflexivity.
Qed.

Lemma NatOfZ : forall n : Z, { p : nat | n = Z.of_nat p \/ n = Z.opp (Z.of_nat p) }.
Proof.
  intros [|p|n].
  - exists O. left. reflexivity.
  - exists (Pos.to_nat p). left. rewrite positive_nat_Z. reflexivity.
  - exists (Pos.to_nat n). right. rewrite positive_nat_Z. reflexivity.
Qed.

Lemma CRmorph_mult_int : forall {R1 R2 : ConstructiveReals}
                           (f : @ConstructiveRealsMorphism R1 R2)
                           (x : CRcarrier R1) (n : Z),
    CRmorph f (CRmult R1 x (CR_of_Q R1 (n # 1)))
    == CRmult R2 (CRmorph f x) (CR_of_Q R2 (n # 1)).
Proof.
  intros. destruct (NatOfZ n) as [p [pos|neg]].
  - subst n. apply CRmorph_mult_pos.
  - subst n.
    apply (CReq_trans
             _ (CRopp R2 (CRmorph  f (CRmult R1 x (CR_of_Q R1 (Z.of_nat p # 1)))))).
    + apply (CReq_trans
               _ (CRmorph f (CRopp R1 (CRmult R1 x (CR_of_Q R1 (Z.of_nat p # 1)))))).
      2: apply CRmorph_opp. apply CRmorph_proper.
      apply (CReq_trans _ (CRmult R1 x (CR_of_Q R1 (- (Z.of_nat p # 1))))).
      * destruct (CRisRingExt R1). apply Rmul_ext.
        -- apply CReq_refl.
        -- apply CR_of_Q_morph. reflexivity.
      * apply (CReq_trans _ (CRmult R1 x (CRopp R1 (CR_of_Q R1 (Z.of_nat p # 1))))).
        -- destruct (CRisRingExt R1). apply Rmul_ext.
           ++ apply CReq_refl.
           ++ apply CR_of_Q_opp.
        -- apply CReq_sym, CRopp_mult_distr_r.
    + apply (CReq_trans
               _ (CRopp R2 (CRmult R2 (CRmorph f x) (CR_of_Q R2 (Z.of_nat p # 1))))).
      * destruct (CRisRingExt R2). apply Ropp_ext. apply CRmorph_mult_pos.
      * apply (CReq_trans
               _ (CRmult R2 (CRmorph f x) (CRopp R2 (CR_of_Q R2 (Z.of_nat p # 1))))).
        -- apply CRopp_mult_distr_r.
        -- destruct (CRisRingExt R2).
           apply Rmul_ext.
           ++ apply CReq_refl.
           ++ apply (CReq_trans _ (CR_of_Q R2 (- (Z.of_nat p # 1)))).
              ** apply CReq_sym, CR_of_Q_opp.
              ** apply CR_of_Q_morph. reflexivity.
Qed.

Lemma CRmorph_mult_inv : forall {R1 R2 : ConstructiveReals}
                           (f : @ConstructiveRealsMorphism R1 R2)
                           (x : CRcarrier R1) (p : positive),
    CRmorph f (CRmult R1 x (CR_of_Q R1 (1 # p)))
    == CRmult R2 (CRmorph f x) (CR_of_Q R2 (1 # p)).
Proof.
  intros. apply (CRmult_eq_reg_r (CR_of_Q R2 (Z.pos p # 1))).
  - left. apply (CRle_lt_trans _ (CR_of_Q R2 0)).
    1:apply CRle_refl. apply CR_of_Q_lt. reflexivity.
  - apply (CReq_trans _ (CRmorph f x)).
    1:apply (CReq_trans
             _ (CRmorph f (CRmult R1 (CRmult R1 x (CR_of_Q R1 (1 # p)))
                                  (CR_of_Q R1 (Z.pos p # 1))))).
    { apply CReq_sym, CRmorph_mult_int. }
    + apply CRmorph_proper.
      apply (CReq_trans
               _ (CRmult R1 x (CRmult R1 (CR_of_Q R1 (1 # p))
                                      (CR_of_Q R1 (Z.pos p # 1))))).
      * destruct (CRisRing R1). apply CReq_sym, Rmul_assoc.
      * apply (CReq_trans _ (CRmult R1 x 1)).
        { apply (Rmul_ext (CRisRingExt R1)). 1:apply CReq_refl.
          apply (CReq_trans _ (CR_of_Q R1 ((1#p) * (Z.pos p # 1)))).
          { apply CReq_sym, CR_of_Q_mult. }
          apply (CReq_trans _ (CR_of_Q R1 1)).
          2:reflexivity.
          apply CR_of_Q_morph. reflexivity.
        }
        apply CRmult_1_r.
    + apply (CReq_trans
                 _ (CRmult R2 (CRmorph f x)
                           (CRmult R2 (CR_of_Q R2 (1 # p)) (CR_of_Q R2 (Z.pos p # 1))))).
      2: apply (Rmul_assoc (CRisRing R2)).
      apply (CReq_trans _ (CRmult R2 (CRmorph f x) 1)).
      { apply CReq_sym, CRmult_1_r. }
      apply (Rmul_ext (CRisRingExt R2)).
      * apply CReq_refl.
      * apply (CReq_trans _ (CR_of_Q R2 1)).
        -- reflexivity.
        -- apply (CReq_trans _ (CR_of_Q R2 ((1#p)*(Z.pos p # 1)))).
           ++ apply CR_of_Q_morph. reflexivity.
           ++ apply CR_of_Q_mult.
Qed.

Lemma CRmorph_mult_rat : forall {R1 R2 : ConstructiveReals}
                           (f : @ConstructiveRealsMorphism R1 R2)
                           (x : CRcarrier R1) (q : Q),
    CRmorph f (CRmult R1 x (CR_of_Q R1 q))
    == CRmult R2 (CRmorph f x) (CR_of_Q R2 q).
Proof.
  intros. destruct q as [a b].
  apply (CReq_trans
           _ (CRmult R2 (CRmorph f (CRmult R1 x (CR_of_Q R1 (a # 1))))
                     (CR_of_Q R2 (1 # b)))).
  - apply (CReq_trans
             _ (CRmorph f (CRmult R1 (CRmult R1 x (CR_of_Q R1 (a # 1)))
                                  (CR_of_Q R1 (1 # b))))).
    2: apply CRmorph_mult_inv. apply CRmorph_proper.
    apply (CReq_trans
             _ (CRmult R1 x (CRmult R1 (CR_of_Q R1 (a # 1))
                                    (CR_of_Q R1 (1 # b))))).
    { apply (Rmul_ext (CRisRingExt R1)). { apply CReq_refl. }
      apply (CReq_trans _ (CR_of_Q R1 ((a#1)*(1#b)))).
      - apply CR_of_Q_morph. unfold Qeq; simpl. rewrite Z.mul_1_r. reflexivity.
      - apply CR_of_Q_mult.
    }
    apply (Rmul_assoc (CRisRing R1)).
  - apply (CReq_trans
             _ (CRmult R2 (CRmult R2 (CRmorph f x) (CR_of_Q R2 (a # 1)))
                       (CR_of_Q R2 (1 # b)))).
    { apply (Rmul_ext (CRisRingExt R2)). { apply CRmorph_mult_int. }
      apply CReq_refl. }
    apply (CReq_trans
             _ (CRmult R2 (CRmorph f x)
                       (CRmult R2 (CR_of_Q R2 (a # 1)) (CR_of_Q R2 (1 # b))))).
    { apply CReq_sym, (Rmul_assoc (CRisRing R2)). }
    apply (Rmul_ext (CRisRingExt R2)). { apply CReq_refl. }
    apply (CReq_trans _ (CR_of_Q R2 ((a#1)*(1#b)))).
    { apply CReq_sym, CR_of_Q_mult. }
    apply CR_of_Q_morph. unfold Qeq; simpl. rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma CRmorph_mult_pos_pos_le : forall {R1 R2 : ConstructiveReals}
                                  (f : @ConstructiveRealsMorphism R1 R2)
                                  (x y : CRcarrier R1),
    CRlt R1 0 y
    -> CRmult R2 (CRmorph f x) (CRmorph f y)
       <= CRmorph f (CRmult R1 x y).
Proof.
  intros. intro abs. destruct (CR_Q_dense R2 _ _ abs) as [q [H1 H2]].
  destruct (CRmorph_rat f q) as [H3 _].
  apply (CRlt_le_trans _ _ _ H1) in H3. clear H1.
  apply CRmorph_increasing_inv in H3.
  apply (CRlt_asym _ _ H3). clear H3.
  destruct (CR_Q_dense R2 _ _ H2) as [r [H1 H3]].
  apply lt_CR_of_Q in H1.
  destruct (CR_archimedean R1 y) as [A Amaj].
  assert (/ ((r - q) * (1 # A)) * (q - r) == - (Z.pos A # 1))%Q as diveq.
  { rewrite Qinv_mult_distr. setoid_replace (q-r)%Q with (-1*(r-q))%Q.
    2:field.
    field_simplify.
    - reflexivity.
    - split.
      + intro H4. inversion H4.
      + intro H4. apply Qlt_minus_iff in H1. rewrite H4 in H1. inversion H1. }
  destruct (CR_Q_dense R1 (CRplus R1 x (CR_of_Q R1 ((q-r) * (1#A)))) x)
    as [s [H4 H5]].
  - apply (CRlt_le_trans _ (CRplus R1 x 0)).
    2: apply CRplus_0_r. apply CRplus_lt_compat_l.
    apply (CRplus_lt_reg_l R1 (CR_of_Q R1 ((r-q) * (1#A)))).
    apply (CRle_lt_trans _ 0).
    1:apply (CRle_trans _ (CR_of_Q R1 ((r-q)*(1#A) + (q-r)*(1#A)))).
    + destruct (CR_of_Q_plus R1 ((r-q)*(1#A)) ((q-r)*(1#A))).
      exact H0.
    + apply (CRle_trans _ (CR_of_Q R1 0)).
      2: apply CRle_refl.
      intro H4. apply lt_CR_of_Q in H4. ring_simplify in H4.
      inversion H4.
    + apply (CRlt_le_trans _ (CR_of_Q R1 ((r - q) * (1 # A)))).
      2: apply CRplus_0_r.
      apply (CRle_lt_trans _ (CR_of_Q R1 0)).
      1:apply CRle_refl. apply CR_of_Q_lt.
      rewrite <- (Qmult_0_r (r-q)). apply Qmult_lt_l.
      * apply Qlt_minus_iff in H1. exact H1.
      * reflexivity.
  - apply (CRmorph_increasing f) in H4.
    destruct (CRmorph_plus f x (CR_of_Q R1 ((q-r) * (1#A)))) as [H6 _].
    apply (CRle_lt_trans _ _ _ H6) in H4. clear H6.
    destruct (CRmorph_rat f s) as [_ H6].
    apply (CRlt_le_trans _ _ _ H4) in H6. clear H4.
    apply (CRmult_lt_compat_r (CRmorph f y)) in H6.
    + destruct (Rdistr_l (CRisRing R2) (CRmorph f x)
                       (CRmorph f (CR_of_Q R1 ((q-r) * (1#A))))
                       (CRmorph f y)) as [H4 _].
      apply (CRle_lt_trans _ _ _ H4) in H6. clear H4.
      apply (CRle_lt_trans _ (CRmult R1 (CR_of_Q R1 s) y)).
      2:{ apply CRmult_lt_compat_r. - exact H. - exact H5. }
      apply (CRmorph_le_inv f).
      apply (CRle_trans _ (CR_of_Q R2 q)).
      { destruct (CRmorph_rat f q). exact H4. }
      apply (CRle_trans _ (CRmult R2 (CR_of_Q R2 s) (CRmorph f y))).
      1:apply (CRle_trans _ (CRplus R2 (CRmult R2 (CRmorph f x) (CRmorph f y))
                                   (CR_of_Q R2 (q-r)))).
      1:apply (CRle_trans _ (CRplus R2 (CR_of_Q R2 r) (CR_of_Q R2 (q - r)))).
      * apply (CRle_trans _ (CR_of_Q R2 (r + (q-r)))).
        -- intro H4. apply lt_CR_of_Q in H4. ring_simplify in H4.
           exact (Qlt_not_le q q H4 (Qle_refl q)).
        -- destruct (CR_of_Q_plus R2 r (q-r)). exact H4.
      * apply CRplus_le_compat_r. intro H4.
        apply (CRlt_asym _ _ H3). exact H4.
      * intro H4. apply (CRlt_asym _ _ H4). clear H4.
        apply (CRlt_trans_flip _ _ _ H6). clear H6.
        apply CRplus_lt_compat_l.
        apply (CRlt_le_trans
                 _ (CRmult R2 (CR_of_Q R2 ((q - r) * (1 # A))) (CRmorph f y))).
        { apply (CRmult_lt_reg_l (CR_of_Q R2 (/((r-q)*(1#A))))).
          1:apply (CRle_lt_trans _ (CR_of_Q R2 0)).
          - apply CRle_refl.
          - apply CR_of_Q_lt, Qinv_lt_0_compat.
            rewrite <- (Qmult_0_r (r-q)). apply Qmult_lt_l.
            + apply Qlt_minus_iff in H1. exact H1.
            + reflexivity.
          - apply (CRle_lt_trans _ (CRopp R2 (CR_of_Q R2 (Z.pos A # 1)))).
            1:apply (CRle_trans _ (CR_of_Q R2 (-(Z.pos A # 1)))).
            1:apply (CRle_trans _ (CR_of_Q R2 ((/ ((r - q) * (1 # A))) * (q - r)))).
            + destruct (CR_of_Q_mult R2 (/ ((r - q) * (1 # A))) (q - r)).
              exact H0.
            + destruct (CR_of_Q_morph R2 (/ ((r - q) * (1 # A)) * (q - r))
                                         (-(Z.pos A # 1))).
              * exact diveq.
              * intro H7. apply lt_CR_of_Q in H7.
                rewrite diveq in H7. exact (Qlt_not_le _ _ H7 (Qle_refl _)).
            + destruct (@CR_of_Q_opp R2 (Z.pos A # 1)). exact H4.
            + apply (CRlt_le_trans _ (CRopp R2 (CRmorph f y))).
              { apply CRopp_gt_lt_contravar.
                apply (CRlt_le_trans _ (CRmorph f (CR_of_Q R1 (Z.pos A # 1)))).
                { apply CRmorph_increasing. exact Amaj. }
                destruct (CRmorph_rat f (Z.pos A # 1)). exact H4.
              }
              apply (CRle_trans _ (CRmult R2 (CRopp R2 1) (CRmorph f y))).
              1:apply (CRle_trans _ (CRopp R2 (CRmult R2 1 (CRmorph f y)))).
              * destruct (Ropp_ext (CRisRingExt R2) (CRmorph f y)
                         (CRmult R2 1 (CRmorph f y))).
                -- apply CReq_sym, (Rmul_1_l (CRisRing R2)).
                -- exact H4.
              * destruct (CRopp_mult_distr_l 1 (CRmorph f y)). exact H4.
              * apply (CRle_trans _ (CRmult R2 (CRmult R2 (CR_of_Q R2 (/ ((r - q) * (1 # A))))
                                             (CR_of_Q R2 ((q - r) * (1 # A))))
                                  (CRmorph f y))).
                { apply CRmult_le_compat_r_half.
                  - apply (CRle_lt_trans _ (CRmorph f 0)).
                    + apply CRmorph_zero.
                    + apply CRmorph_increasing. exact H.
                  - apply (CRle_trans _ (CR_of_Q R2 ((/ ((r - q) * (1 # A)))
                                       * ((q - r) * (1 # A))))).
                    1:apply (CRle_trans _ (CR_of_Q R2 (-1))).
                    1:apply (CRle_trans _ (CRopp R2 (CR_of_Q R2 1))).
                    + destruct (Ropp_ext (CRisRingExt R2) 1 (CR_of_Q R2 1)).
                      * reflexivity.
                      * exact H4.
                    + destruct (@CR_of_Q_opp R2 1). exact H0.
                    + destruct (CR_of_Q_morph R2 (-1) (/ ((r - q) * (1 # A)) * ((q - r) * (1 # A)))).
                      * field. split.
                        -- intro H4. inversion H4.
                        -- intro H4. apply Qlt_minus_iff in H1.
                           rewrite H4 in H1. inversion H1.
                      * exact H4.
                    + destruct (CR_of_Q_mult R2 (/ ((r - q) * (1 # A))) ((q - r) * (1 # A))).
                      exact H4.
                }
                destruct (Rmul_assoc (CRisRing R2) (CR_of_Q R2 (/ ((r - q) * (1 # A))))
                                     (CR_of_Q R2 ((q - r) * (1 # A)))
                                     (CRmorph f y)).
                exact H0.
        }
        apply CRmult_le_compat_r_half.
        -- apply (CRle_lt_trans _ (CRmorph f 0)).
           ++ apply CRmorph_zero.
           ++ apply CRmorph_increasing. exact H.
        -- destruct (CRmorph_rat f ((q - r) * (1 # A))). exact H0.
      * apply (CRle_trans _ (CRmorph f (CRmult R1 y (CR_of_Q R1 s)))).
        1:apply (CRle_trans _ (CRmult R2 (CRmorph f y) (CR_of_Q R2 s))).
        -- destruct (Rmul_comm (CRisRing R2) (CRmorph f y) (CR_of_Q R2 s)).
           exact H0.
        -- destruct (CRmorph_mult_rat f y s). exact H0.
        -- destruct (CRmorph_proper f (CRmult R1 y (CR_of_Q R1 s))
                                 (CRmult R1 (CR_of_Q R1 s) y)).
           ++ apply (Rmul_comm (CRisRing R1)).
           ++ exact H4.
    + apply (CRle_lt_trans _ (CRmorph f 0)).
      * apply CRmorph_zero.
      * apply CRmorph_increasing. exact H.
Qed.

Lemma CRmorph_mult_pos_pos : forall {R1 R2 : ConstructiveReals}
                               (f : @ConstructiveRealsMorphism R1 R2)
                               (x y : CRcarrier R1),
    CRlt R1 0 y
    -> CRmorph f (CRmult R1 x y)
       == CRmult R2 (CRmorph f x) (CRmorph f y).
Proof.
  split.
  { apply CRmorph_mult_pos_pos_le. exact H. }
  intro abs. destruct (CR_Q_dense R2 _ _ abs) as [q [H1 H2]].
  destruct (CRmorph_rat f q) as [_ H3].
  apply (CRle_lt_trans _ _ _ H3) in H2. clear H3.
  apply CRmorph_increasing_inv in H2.
  apply (CRlt_asym _ _ H2). clear H2.
  destruct (CR_Q_dense R2 _ _ H1) as [r [H2 H3]].
  apply lt_CR_of_Q in H3.
  destruct (CR_archimedean R1 y) as [A Amaj].
  destruct (CR_Q_dense R1 x (CRplus R1 x (CR_of_Q R1 ((q-r) * (1#A)))))
    as [s [H4 H5]].
  - apply (CRle_lt_trans _ (CRplus R1 x 0)).
    + apply CRplus_0_r.
    + apply CRplus_lt_compat_l.
      apply (CRle_lt_trans _ (CR_of_Q R1 0)).
      * apply CRle_refl.
      * apply CR_of_Q_lt.
        rewrite <- (Qmult_0_r (q-r)). apply Qmult_lt_l.
        -- apply Qlt_minus_iff in H3. exact H3.
        -- reflexivity.
  - apply (CRmorph_increasing f) in H5.
    destruct (CRmorph_plus f x (CR_of_Q R1 ((q-r) * (1#A)))) as [_ H6].
    apply (CRlt_le_trans _ _ _ H5) in H6. clear H5.
    destruct (CRmorph_rat f s) as [H5 _ ].
    apply (CRle_lt_trans _ _ _ H5) in H6. clear H5.
    apply (CRmult_lt_compat_r (CRmorph f y)) in H6.
    2:{ apply (CRle_lt_trans _ (CRmorph f 0)).
        - apply CRmorph_zero.
        - apply CRmorph_increasing. exact H. }
    apply (CRlt_le_trans _ (CRmult R1 (CR_of_Q R1 s) y)).
    { apply CRmult_lt_compat_r. - exact H. - exact H4. }
    clear H4.
    apply (CRmorph_le_inv f).
    apply (CRle_trans _ (CR_of_Q R2 q)).
    2: destruct (CRmorph_rat f q); exact H0.
    apply (CRle_trans _ (CRmult R2 (CR_of_Q R2 s) (CRmorph f y))).
    1:apply (CRle_trans _ (CRmorph f (CRmult R1 y (CR_of_Q R1 s)))).
    + destruct (CRmorph_proper f (CRmult R1 (CR_of_Q R1 s) y)
                               (CRmult R1 y (CR_of_Q R1 s))).
      * apply (Rmul_comm (CRisRing R1)).
      * exact H4.
    + apply (CRle_trans _ (CRmult R2 (CRmorph f y) (CR_of_Q R2 s))).
      * exact (proj2 (CRmorph_mult_rat f y s)).
      * destruct (Rmul_comm (CRisRing R2) (CR_of_Q R2 s) (CRmorph f y)).
        exact H0.
    + intro H5. apply (CRlt_asym _ _ H5). clear H5.
      apply (CRlt_trans _ _ _ H6). clear H6.
      apply (CRle_lt_trans
               _ (CRplus R2
                         (CRmult R2 (CRmorph f x) (CRmorph f y))
                         (CRmult R2 (CRmorph f (CR_of_Q R1 ((q - r) * (1 # A))))
                                 (CRmorph f y)))).
      { apply (Rdistr_l (CRisRing R2)). }
      apply (CRle_lt_trans
               _ (CRplus R2 (CR_of_Q R2 r)
                         (CRmult R2 (CRmorph f (CR_of_Q R1 ((q - r) * (1 # A))))
                                 (CRmorph f y)))).
      { apply CRplus_le_compat_r. intro H5. apply (CRlt_asym _ _ H5 H2). }
      clear H2.
      apply (CRle_lt_trans
               _ (CRplus R2 (CR_of_Q R2 r)
                         (CRmult R2 (CR_of_Q R2 ((q - r) * (1 # A)))
                                 (CRmorph f y)))).
      { apply CRplus_le_compat_l, CRmult_le_compat_r_half.
        - apply (CRle_lt_trans _ (CRmorph f 0)).
          + apply CRmorph_zero.
          + apply CRmorph_increasing. exact H.
        - destruct (CRmorph_rat f ((q - r) * (1 # A))). exact H2. }
      apply (CRlt_le_trans _ (CRplus R2 (CR_of_Q R2 r)
                                     (CR_of_Q R2 ((q - r))))).
      * apply CRplus_lt_compat_l.
        apply (CRmult_lt_reg_l (CR_of_Q R2 (/((q - r) * (1 # A))))).
        { apply (CRle_lt_trans _ (CR_of_Q R2 0)).
          { apply CRle_refl. }
          apply CR_of_Q_lt, Qinv_lt_0_compat.
          rewrite <- (Qmult_0_r (q-r)). apply Qmult_lt_l.
          - apply Qlt_minus_iff in H3. exact H3.
          - reflexivity. }
        apply (CRle_lt_trans _ (CRmorph f y)).
        -- apply (CRle_trans _ (CRmult R2 (CRmult R2 (CR_of_Q R2 (/ ((q - r) * (1 # A))))
                                                  (CR_of_Q R2 ((q - r) * (1 # A))))
                                       (CRmorph f y))).
           { exact (proj2 (Rmul_assoc (CRisRing R2) (CR_of_Q R2 (/ ((q - r) * (1 # A))))
                                      (CR_of_Q R2 ((q - r) * (1 # A)))
                                      (CRmorph f y))). }
           apply (CRle_trans _ (CRmult R2 1 (CRmorph f y))).
           ++ apply CRmult_le_compat_r_half.
              { apply (CRle_lt_trans _ (CRmorph f 0)).
                { apply CRmorph_zero. }
                apply CRmorph_increasing. exact H. }
              apply (CRle_trans
                       _ (CR_of_Q R2 ((/ ((q - r) * (1 # A))) * ((q - r) * (1 # A))))).
              { exact (proj1 (CR_of_Q_mult R2 (/ ((q - r) * (1 # A))) ((q - r) * (1 # A)))). }
              apply (CRle_trans _ (CR_of_Q R2 1)).
              { destruct (CR_of_Q_morph R2 (/ ((q - r) * (1 # A)) * ((q - r) * (1 # A))) 1).
                - field_simplify.
                  { reflexivity. }
                  split.
                  { intro H5. inversion H5. }
                  intro H5. apply Qlt_minus_iff in H3.
                  rewrite H5 in H3. inversion H3.
                - exact H2.
              }
              apply CRle_refl.
           ++ destruct (Rmul_1_l (CRisRing R2) (CRmorph f y)).
              intro H5. contradiction.
        -- apply (CRlt_le_trans _ (CR_of_Q R2 (Z.pos A # 1))).
           1:apply (CRlt_le_trans _ (CRmorph f (CR_of_Q R1 (Z.pos A # 1)))).
           { apply CRmorph_increasing. exact Amaj. }
           { exact (proj2 (CRmorph_rat f (Z.pos A # 1))). }
           apply (CRle_trans _ (CR_of_Q R2 ((/ ((q - r) * (1 # A))) * (q - r)))).
           2: exact (proj2 (CR_of_Q_mult R2 (/ ((q - r) * (1 # A))) (q - r))).
           destruct (CR_of_Q_morph R2 (Z.pos A # 1) (/ ((q - r) * (1 # A)) * (q - r))).
           { field_simplify. { reflexivity. }
             split.
             - intro H5. inversion H5.
             - intro H5. apply Qlt_minus_iff in H3.
               rewrite H5 in H3. inversion H3. }
           exact H2.
      * apply (CRle_trans _ (CR_of_Q R2 (r + (q-r)))).
        -- exact (proj1 (CR_of_Q_plus R2 r (q-r))).
        -- destruct (CR_of_Q_morph R2 (r + (q-r)) q).
           ++ ring.
           ++ exact H2.
Qed.

Lemma CRmorph_mult : forall {R1 R2 : ConstructiveReals}
                       (f : @ConstructiveRealsMorphism R1 R2)
                       (x y : CRcarrier R1),
    CRmorph f (CRmult R1 x y)
    == CRmult R2 (CRmorph f x) (CRmorph f y).
Proof.
  intros.
  destruct (CR_archimedean R1 (CRopp R1 y)) as [p pmaj].
  apply (CRplus_eq_reg_r (CRmult R2 (CRmorph f x)
                                    (CR_of_Q R2 (Z.pos p # 1)))).
  apply (CReq_trans _ (CRmorph f (CRmult R1 x (CRplus R1 y (CR_of_Q R1 (Z.pos p # 1)))))).
  - apply (CReq_trans _ (CRplus R2 (CRmorph f (CRmult R1 x y))
                                (CRmorph f (CRmult R1 x (CR_of_Q R1 (Z.pos p # 1)))))).
    + apply (Radd_ext (CRisRingExt R2)).
      * apply CReq_refl.
      * apply CReq_sym, CRmorph_mult_int.
    + apply (CReq_trans _ (CRmorph f (CRplus R1 (CRmult R1 x y)
                                             (CRmult R1 x (CR_of_Q R1 (Z.pos p # 1)))))).
      * apply CReq_sym, CRmorph_plus.
      * apply CRmorph_proper.
        apply CReq_sym, CRmult_plus_distr_l.
  - apply (CReq_trans _ (CRmult R2 (CRmorph f x)
                                (CRmorph f (CRplus R1 y (CR_of_Q R1 (Z.pos p # 1)))))).
    + apply CRmorph_mult_pos_pos.
      apply (CRplus_lt_compat_l R1 y) in pmaj.
      apply (CRle_lt_trans _ (CRplus R1 y (CRopp R1 y))).
      2: exact pmaj. apply (CRisRing R1).
    + apply (CReq_trans _ (CRmult R2 (CRmorph f x)
                                  (CRplus R2 (CRmorph f y) (CR_of_Q R2 (Z.pos p # 1))))).
      * apply (Rmul_ext (CRisRingExt R2)).
        -- apply CReq_refl.
        -- apply (CReq_trans _ (CRplus R2 (CRmorph f y)
                                       (CRmorph f (CR_of_Q R1 (Z.pos p # 1))))).
           ++ apply CRmorph_plus.
           ++ apply (Radd_ext (CRisRingExt R2)).
              ** apply CReq_refl.
              ** apply CRmorph_rat.
      * apply CRmult_plus_distr_l.
Qed.

Lemma CRmorph_appart : forall {R1 R2 : ConstructiveReals}
                         (f : @ConstructiveRealsMorphism R1 R2)
                         (x y : CRcarrier R1)
                         (app : x ≶ y),
    CRmorph f x ≶ CRmorph f y.
Proof.
  intros. destruct app.
  - left. apply CRmorph_increasing. exact c.
  - right. apply CRmorph_increasing. exact c.
Defined.

Lemma CRmorph_appart_zero : forall {R1 R2 : ConstructiveReals}
                              (f : @ConstructiveRealsMorphism R1 R2)
                              (x : CRcarrier R1)
                              (app : x ≶ 0),
    CRmorph f x ≶ 0.
Proof.
  intros. destruct app.
  - left. apply (CRlt_le_trans _ (CRmorph f 0)).
    + apply CRmorph_increasing. exact c.
    + exact (proj2 (CRmorph_zero f)).
  - right. apply (CRle_lt_trans  _ (CRmorph f 0)).
    + exact (proj1 (CRmorph_zero f)).
    + apply CRmorph_increasing. exact c.
Defined.

Lemma CRmorph_inv : forall {R1 R2 : ConstructiveReals}
                      (f : @ConstructiveRealsMorphism R1 R2)
                      (x : CRcarrier R1)
                      (xnz : x ≶ 0)
                      (fxnz : CRmorph f x ≶ 0),
    CRmorph f ((/ x) xnz)
    == (/ CRmorph f x) fxnz.
Proof.
  intros. apply (CRmult_eq_reg_r (CRmorph f x)).
  - destruct fxnz.
    + right. exact c.
    + left. exact c.
  - apply (CReq_trans _ 1).
    2: apply CReq_sym, CRinv_l.
    apply (CReq_trans _ (CRmorph f (CRmult R1 ((/ x) xnz) x))).
    + apply CReq_sym, CRmorph_mult.
    + apply (CReq_trans _ (CRmorph f 1)).
      * apply CRmorph_proper. apply CRinv_l.
      * apply CRmorph_one.
Qed.

Lemma CRmorph_rat_cv
  : forall {R1 R2 : ConstructiveReals}
           (qn : nat -> Q),
  CR_cauchy R1 (fun n => CR_of_Q R1 (qn n))
  -> CR_cauchy R2 (fun n => CR_of_Q R2 (qn n)).
Proof.
  intros. intro p. destruct (H p) as [n nmaj].
  exists n. intros. specialize (nmaj i j H0 H1).
  unfold CRminus. rewrite <- CR_of_Q_opp, <- CR_of_Q_plus, CR_of_Q_abs.
  unfold CRminus in nmaj. rewrite <- CR_of_Q_opp, <- CR_of_Q_plus, CR_of_Q_abs in nmaj.
  apply CR_of_Q_le. destruct (Q_dec (Qabs (qn i + - qn j)) (1#p)).
  - destruct s.
    + apply Qlt_le_weak, q.
    + exfalso.
      apply (Qlt_not_le _ _ q). apply (CR_of_Q_lt R1) in q. contradiction.
  - rewrite q. apply Qle_refl.
Qed.

Definition CR_Q_limit {R : ConstructiveReals} (x : CRcarrier R) (n:nat)
  : { q:Q  &  x < CR_of_Q R q < x + CR_of_Q R (1 # Pos.of_nat n) }.
Proof.
  apply (CR_Q_dense R x (x + CR_of_Q R (1 # Pos.of_nat n))).
  rewrite <- (CRplus_0_r x). rewrite CRplus_assoc.
  apply CRplus_lt_compat_l. rewrite CRplus_0_l. apply CR_of_Q_pos.
  reflexivity.
Qed.

Lemma CR_Q_limit_cv : forall {R : ConstructiveReals} (x : CRcarrier R),
    CR_cv R (fun n => CR_of_Q R (let (q,_) := CR_Q_limit x n in q)) x.
Proof.
  intros R x p. exists (Pos.to_nat p).
  intros. destruct (CR_Q_limit x i). rewrite CRabs_right.
  - apply (CRplus_le_reg_r x). unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_comm.
    apply (CRle_trans _ (x + CR_of_Q R (1 # Pos.of_nat i))).
    + apply CRlt_asym, p0.
    + apply CRplus_le_compat_l, CR_of_Q_le.
      unfold Qle, Qnum, Qden. rewrite Z.mul_1_l, Z.mul_1_l.
      apply Pos2Z.pos_le_pos, Pos2Nat.inj_le. rewrite Nat2Pos.id.
      * exact H.
      * destruct i.
        -- exfalso. inversion H. pose proof (Pos2Nat.is_pos p).
           rewrite H1 in H0. inversion H0.
        -- discriminate.
  - rewrite <- (CRplus_opp_r x). apply CRplus_le_compat_r, CRlt_asym, p0.
Qed.

(* We call this morphism slow to remind that it should only be used
   for proofs, not for computations. *)
Definition SlowMorph {R1 R2 : ConstructiveReals}
  : CRcarrier R1 -> CRcarrier R2
  := fun x => let (y,_) := CR_complete R2 _ (CRmorph_rat_cv _ (Rcv_cauchy_mod _ x (CR_Q_limit_cv x)))
              in y.

Lemma CauchyMorph_rat : forall {R1 R2 : ConstructiveReals} (q : Q),
    SlowMorph (CR_of_Q R1 q) == CR_of_Q R2 q.
Proof.
  intros. unfold SlowMorph.
  destruct (CR_complete R2 _
       (CRmorph_rat_cv _
          (Rcv_cauchy_mod
             (fun n : nat => CR_of_Q R1 (let (q0, _) := CR_Q_limit (CR_of_Q R1 q) n in q0))
             (CR_of_Q R1 q) (CR_Q_limit_cv (CR_of_Q R1 q))))).
  apply (CR_cv_unique _ _ _ c).
  intro p. exists (Pos.to_nat p). intros.
  destruct (CR_Q_limit (CR_of_Q R1 q) i). rewrite CRabs_right.
  - apply (CRplus_le_reg_r (CR_of_Q R2 q)). unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_comm.
    rewrite <- CR_of_Q_plus. apply CR_of_Q_le.
    destruct (Q_dec x0 (q + (1 # p))%Q).
    + destruct s.
      * apply Qlt_le_weak, q0.
      * exfalso. pose proof (CR_of_Q_lt R1 _ _ q0).
        apply (CRlt_asym _ _ H0). apply (CRlt_le_trans _ _ _ (snd p0)). clear H0.
        rewrite <- CR_of_Q_plus. apply CR_of_Q_le. apply Qplus_le_r.
        unfold Qle, Qnum, Qden. rewrite Z.mul_1_l, Z.mul_1_l.
        apply Pos2Z.pos_le_pos, Pos2Nat.inj_le. rewrite Nat2Pos.id.
        -- exact H.
        -- destruct i.
           ++ exfalso. inversion H. pose proof (Pos2Nat.is_pos p).
              rewrite H1 in H0. inversion H0.
           ++ discriminate.
    + rewrite q0. apply Qle_refl.
  - rewrite <- (CRplus_opp_r (CR_of_Q R2 q)). apply CRplus_le_compat_r, CR_of_Q_le.
    destruct (Q_dec q x0).
    + destruct s.
      * apply Qlt_le_weak, q0.
      * exfalso. apply (CRlt_asym _ _ (fst p0)). apply CR_of_Q_lt. exact q0.
    + rewrite q0. apply Qle_refl.
Qed.

(* The increasing property of morphisms, when the left bound is rational. *)
Lemma SlowMorph_increasing_Qr
  : forall {R1 R2 : ConstructiveReals} (x : CRcarrier R1) (q : Q),
    CR_of_Q R1 q < x -> CR_of_Q R2 q < SlowMorph x.
Proof.
  intros.
  unfold SlowMorph;
  destruct (CR_complete R2 _
       (CRmorph_rat_cv _
          (Rcv_cauchy_mod (fun n : nat => CR_of_Q R1 (let (q0, _) := CR_Q_limit x n in q0)) x
             (CR_Q_limit_cv x)))).
  destruct (CR_Q_dense R1 _ _ H) as [r [H0 H1]].
  apply lt_CR_of_Q in H0.
  apply (CRlt_le_trans _ (CR_of_Q R2 r)).
  - apply CR_of_Q_lt, H0.
  - assert (forall n:nat, le O n -> CR_of_Q R2 r <= CR_of_Q R2 (let (q0, _) := CR_Q_limit x n in q0)).
    { intros. apply CR_of_Q_le. destruct (CR_Q_limit x n).
      destruct (Q_dec r x1).
      - destruct s.
        + apply Qlt_le_weak, q0.
        + exfalso. apply (CR_of_Q_lt R1) in q0.
          apply (CRlt_asym _ _ q0). exact (CRlt_trans _ _ _ H1 (fst p)).
      - rewrite q0. apply Qle_refl. }
    exact (CR_cv_bound_down _ _ _ O H2 c).
Qed.

(* The increasing property of morphisms, when the right bound is rational. *)
Lemma SlowMorph_increasing_Ql
  : forall {R1 R2 : ConstructiveReals} (x : CRcarrier R1) (q : Q),
    x < CR_of_Q R1 q -> SlowMorph x < CR_of_Q R2 q.
Proof.
  intros.
  unfold SlowMorph;
  destruct (CR_complete R2 _
       (CRmorph_rat_cv _
          (Rcv_cauchy_mod (fun n : nat => CR_of_Q R1 (let (q0, _) := CR_Q_limit x n in q0)) x
             (CR_Q_limit_cv x)))).
  assert (CR_cv R1 (fun n => CR_of_Q R1 (let (q0, _) := CR_Q_limit x n in q0)
                             + CR_of_Q R1 (1 # Pos.of_nat n)) x).
  { apply (CR_cv_proper _ (x+0)).
    - apply CR_cv_plus.
      + apply CR_Q_limit_cv.
      + intro p. exists (Pos.to_nat p). intros.
        unfold CRminus. rewrite CRopp_0, CRplus_0_r. rewrite CRabs_right.
        * apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
          apply Pos2Z.pos_le_pos, Pos2Nat.inj_le. rewrite Nat2Pos.id.
          -- exact H0.
          -- destruct i.
             ++ inversion H0. pose proof (Pos2Nat.is_pos p).
                rewrite H2 in H1. inversion H1.
             ++ discriminate.
        * apply CR_of_Q_le. discriminate.
    - rewrite CRplus_0_r. reflexivity. }
  pose proof (CR_cv_open_above _ _ _ H0 H) as [n nmaj].
  apply (CRle_lt_trans _ (CR_of_Q R2 (let (q0, _) := CR_Q_limit x n in
                                      q0 + (1 # Pos.of_nat n)))).
  - apply (CR_cv_bound_up (fun n : nat => CR_of_Q R2 (let (q0, _) := CR_Q_limit x n in q0)) _ _ n).
    2: exact c. intros. destruct (CR_Q_limit x n0), (CR_Q_limit x n).
    apply CR_of_Q_le, Qlt_le_weak. apply (lt_CR_of_Q R1).
    apply (CRlt_le_trans _ _ _ (snd p)).
    apply (CRle_trans _ (CR_of_Q R1 x2 + CR_of_Q R1 (1 # Pos.of_nat n0))).
    + apply CRplus_le_compat_r. apply CRlt_asym, p0.
    + rewrite <- CR_of_Q_plus. apply CR_of_Q_le. apply Qplus_le_r.
      unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
      apply Pos2Z.pos_le_pos, Pos2Nat.inj_le.
      destruct n.
      * destruct n0.
        -- apply Nat.le_refl.
        -- rewrite (Nat2Pos.id (S n0)).
           ++ apply -> Nat.succ_le_mono; apply Nat.le_0_l.
           ++ discriminate.
      * destruct n0.
        -- exfalso; inversion H1.
        -- rewrite Nat2Pos.id, Nat2Pos.id.
           ++ exact H1.
           ++ discriminate.
           ++ discriminate.
  - specialize (nmaj n (Nat.le_refl n)).
    destruct (CR_Q_limit x n). apply CR_of_Q_lt.
    rewrite <- CR_of_Q_plus in nmaj. apply lt_CR_of_Q in nmaj. exact nmaj.
Qed.

Lemma SlowMorph_increasing : forall {R1 R2 : ConstructiveReals} (x y : CRcarrier R1),
    x < y -> @SlowMorph R1 R2 x < SlowMorph y.
Proof.
  intros.
  destruct (CR_Q_dense R1 _ _ H) as [q [H0 H1]].
  apply (CRlt_trans _ (CR_of_Q R2 q)).
  - apply SlowMorph_increasing_Ql. exact H0.
  - apply SlowMorph_increasing_Qr. exact H1.
Qed.


(* We call this morphism slow to remind that it should only be used
   for proofs, not for computations. *)
Definition SlowConstructiveRealsMorphism {R1 R2 : ConstructiveReals}
  : @ConstructiveRealsMorphism R1 R2
  := Build_ConstructiveRealsMorphism
       R1 R2 SlowMorph CauchyMorph_rat
       SlowMorph_increasing.

Lemma CRmorph_abs : forall {R1 R2 : ConstructiveReals}
                      (f : @ConstructiveRealsMorphism R1 R2)
                      (x : CRcarrier R1),
    CRabs R2 (CRmorph f x) == CRmorph f (CRabs R1 x).
Proof.
  assert (forall {R1 R2 : ConstructiveReals}
            (f : @ConstructiveRealsMorphism R1 R2)
            (x : CRcarrier R1),
             CRabs R2 (CRmorph f x) <= CRmorph f (CRabs R1 x)).
  { intros. rewrite <- CRabs_def. split.
    - apply CRmorph_le.
      pose proof (CRabs_def _ x (CRabs R1 x)) as [_ H].
      apply H, CRle_refl.
    - apply (CRle_trans _ (CRmorph f (CRopp R1 x))).
      + apply CRmorph_opp.
      + apply CRmorph_le.
        pose proof (CRabs_def _ x (CRabs R1 x)) as [_ H].
        apply H, CRle_refl. }
  intros. split. 2: apply H.
  apply (CRmorph_le_inv (@SlowConstructiveRealsMorphism R2 R1)).
  apply (CRle_trans _ (CRabs R1 x)).
  - apply (Endomorph_id
             (CRmorph_compose f (@SlowConstructiveRealsMorphism R2 R1))).
  - apply (CRle_trans
             _ (CRabs R1 (CRmorph (@SlowConstructiveRealsMorphism R2 R1) (CRmorph f x)))).
    + apply CRabs_morph.
      apply CReq_sym, (Endomorph_id
                         (CRmorph_compose f (@SlowConstructiveRealsMorphism R2 R1))).
    + apply H.
Qed.

Lemma CRmorph_cv : forall {R1 R2 : ConstructiveReals}
                     (f : @ConstructiveRealsMorphism R1 R2)
                     (un : nat -> CRcarrier R1)
                     (l : CRcarrier R1),
    CR_cv R1 un l
    -> CR_cv R2 (fun n => CRmorph f (un n)) (CRmorph f l).
Proof.
  intros. intro p. specialize (H p) as [n H].
  exists n. intros. specialize (H i H0).
  unfold CRminus. rewrite <- CRmorph_opp, <- CRmorph_plus, CRmorph_abs.
  rewrite <- (CRmorph_rat f (1#p)). apply CRmorph_le. exact H.
Qed.

Lemma CRmorph_cauchy_reverse : forall {R1 R2 : ConstructiveReals}
                     (f : @ConstructiveRealsMorphism R1 R2)
                     (un : nat -> CRcarrier R1),
    CR_cauchy R2 (fun n => CRmorph f (un n))
    -> CR_cauchy R1 un.
Proof.
  intros. intro p. specialize (H p) as [n H].
  exists n. intros. specialize (H i j H0 H1).
  unfold CRminus in H. rewrite <- CRmorph_opp, <- CRmorph_plus, CRmorph_abs in H.
  rewrite <- (CRmorph_rat f (1#p)) in H.
  apply (CRmorph_le_inv f) in H. exact H.
Qed.
