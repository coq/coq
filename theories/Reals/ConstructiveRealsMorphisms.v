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
    it captures a concept with a strong notion of uniqueness. *)

Require Import QArith.
Require Import Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveCauchyRealsMult.
Require Import ConstructiveRIneq.


Record ConstructiveRealsMorphism (R1 R2 : ConstructiveReals) : Set :=
  {
    CRmorph : CRcarrier R1 -> CRcarrier R2;
    CRmorph_rat : forall q : Q,
        orderEq _ (CRlt R2) (CRmorph (CR_of_Q R1 q)) (CR_of_Q R2 q);
    CRmorph_increasing : forall x y : CRcarrier R1,
        CRlt R1 x y -> CRlt R2 (CRmorph x) (CRmorph y);
  }.


Lemma CRmorph_increasing_inv
  : forall (R1 R2 : ConstructiveReals)
      (f : ConstructiveRealsMorphism R1 R2)
      (x y : CRcarrier R1),
    CRlt R2 (CRmorph _ _ f x) (CRmorph _ _ f y)
    -> CRlt R1 x y.
Proof.
  intros. destruct (CR_Q_dense R2 _ _ H) as [q [H0 H1]].
  destruct (CR_Q_dense R2 _ _ H0) as [r [H2 H3]].
  apply lt_CR_of_Q, (CR_of_Q_lt R1) in H3.
  destruct (CRltLinear R1).
  destruct (s _ x _ H3).
  - exfalso. apply (CRmorph_increasing _ _ f) in c.
    destruct (CRmorph_rat _ _ f r) as [H4 _].
    apply (CRle_lt_trans R2 _ _ _ H4) in c. clear H4.
    exact (CRlt_asym R2 _ _ c H2).
  - clear H2 H3 r. apply (CRlt_trans R1 _ _ _ c). clear c.
    destruct (CR_Q_dense R2 _ _ H1) as [t [H2 H3]].
    apply lt_CR_of_Q, (CR_of_Q_lt R1) in H2.
    destruct (s _ y _ H2). exact c.
    exfalso. apply (CRmorph_increasing _ _ f) in c.
    destruct (CRmorph_rat _ _ f t) as [_ H4].
    apply (CRlt_le_trans R2 _ _ _ c) in H4. clear c.
    exact (CRlt_asym R2 _ _ H4 H3).
Qed.

Lemma CRmorph_unique : forall (R1 R2 : ConstructiveReals)
                         (f g : ConstructiveRealsMorphism R1 R2)
                         (x : CRcarrier R1),
    orderEq _ (CRlt R2) (CRmorph _ _ f x) (CRmorph _ _ g x).
Proof.
  split.
  - intro abs. destruct (CR_Q_dense R2 _ _ abs) as [q [H H0]].
    destruct (CRmorph_rat _ _ f q) as [H1 _].
    apply (CRlt_le_trans R2 _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    destruct (CRmorph_rat _ _ g q) as [_ H2].
    apply (CRle_lt_trans R2 _ _ _ H2) in H0. clear H2.
    apply CRmorph_increasing_inv in H0.
    exact (CRlt_asym R1 _ _ H0 H1).
  - intro abs. destruct (CR_Q_dense R2 _ _ abs) as [q [H H0]].
    destruct (CRmorph_rat _ _ f q) as [_ H1].
    apply (CRle_lt_trans R2 _ _ _ H1) in H0. clear H1.
    apply CRmorph_increasing_inv in H0.
    destruct (CRmorph_rat _ _ g q) as [H2 _].
    apply (CRlt_le_trans R2 _ _ _ H) in H2. clear H.
    apply CRmorph_increasing_inv in H2.
    exact (CRlt_asym R1 _ _ H0 H2).
Qed.


(* The identity is the only endomorphism of constructive reals.
   For any ConstructiveReals R1, R2 and any morphisms
   f : R1 -> R2 and g : R2 -> R1,
   f and g are isomorphisms and are inverses of each other. *)
Lemma Endomorph_id : forall (R : ConstructiveReals) (f : ConstructiveRealsMorphism R R)
                       (x : CRcarrier R),
    orderEq _ (CRlt R) (CRmorph _ _ f x) x.
Proof.
  split.
  - intro abs. destruct (CR_Q_dense R _ _ abs) as [q [H0 H1]].
    destruct (CRmorph_rat _ _ f q) as [H _].
    apply (CRlt_le_trans R _ _ _ H0) in H. clear H0.
    apply CRmorph_increasing_inv in H.
    exact (CRlt_asym R _ _ H1 H).
  - intro abs. destruct (CR_Q_dense R _ _ abs) as [q [H0 H1]].
    destruct (CRmorph_rat _ _ f q) as [_ H].
    apply (CRle_lt_trans R _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    exact (CRlt_asym R _ _ H1 H0).
Qed.

Lemma CRmorph_proper : forall (R1 R2 : ConstructiveReals)
                         (f : ConstructiveRealsMorphism R1 R2)
                         (x y : CRcarrier R1),
    orderEq _ (CRlt R1) x y
    -> orderEq _ (CRlt R2) (CRmorph _ _ f x) (CRmorph _ _ f y).
Proof.
  split.
  - intro abs. apply CRmorph_increasing_inv in abs.
    destruct H. contradiction.
  - intro abs. apply CRmorph_increasing_inv in abs.
    destruct H. contradiction.
Qed.

Definition CRmorph_compose (R1 R2 R3 : ConstructiveReals)
           (f : ConstructiveRealsMorphism R1 R2)
           (g : ConstructiveRealsMorphism R2 R3)
  : ConstructiveRealsMorphism R1 R3.
Proof.
  apply (Build_ConstructiveRealsMorphism
           R1 R3 (fun x:CRcarrier R1 => CRmorph _ _ g (CRmorph _ _ f x))).
  - intro q. apply (CReq_trans R3 _ (CRmorph R2 R3 g (CR_of_Q R2 q))).
    apply CRmorph_proper. apply CRmorph_rat. apply CRmorph_rat.
  - intros. apply CRmorph_increasing. apply CRmorph_increasing. exact H.
Defined.

Lemma CRmorph_le : forall (R1 R2 : ConstructiveReals)
                     (f : ConstructiveRealsMorphism R1 R2)
                     (x y : CRcarrier R1),
    orderLe _ (CRlt R1) x y
    -> orderLe _ (CRlt R2) (CRmorph _ _ f x) (CRmorph _ _ f y).
Proof.
  intros. intro abs. apply CRmorph_increasing_inv in abs. contradiction.
Qed.

Lemma CRmorph_le_inv : forall (R1 R2 : ConstructiveReals)
                         (f : ConstructiveRealsMorphism R1 R2)
                         (x y : CRcarrier R1),
    orderLe _ (CRlt R2) (CRmorph _ _ f x) (CRmorph _ _ f y)
    -> orderLe _ (CRlt R1) x y.
Proof.
  intros. intro abs. apply (CRmorph_increasing _ _ f) in abs. contradiction.
Qed.

Lemma CRmorph_zero : forall (R1 R2 : ConstructiveReals)
                       (f : ConstructiveRealsMorphism R1 R2),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRzero R1)) (CRzero R2).
Proof.
  intros. apply (CReq_trans R2 _ (CRmorph _ _ f (CR_of_Q R1 0))).
  apply CRmorph_proper. apply CReq_sym, CR_of_Q_zero.
  apply (CReq_trans R2 _ (CR_of_Q R2 0)).
  apply CRmorph_rat. apply CR_of_Q_zero.
Qed.

Lemma CRmorph_one : forall (R1 R2 : ConstructiveReals)
                      (f : ConstructiveRealsMorphism R1 R2),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRone R1)) (CRone R2).
Proof.
  intros. apply (CReq_trans R2 _ (CRmorph _ _ f (CR_of_Q R1 1))).
  apply CRmorph_proper. apply CReq_sym, CR_of_Q_one.
  apply (CReq_trans R2 _ (CR_of_Q R2 1)).
  apply CRmorph_rat. apply CR_of_Q_one.
Qed.

Lemma CRmorph_opp : forall (R1 R2 : ConstructiveReals)
                      (f : ConstructiveRealsMorphism R1 R2)
                      (x : CRcarrier R1),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRopp R1 x))
            (CRopp R2 (CRmorph _ _ f x)).
Proof.
  split.
  - intro abs.
    destruct (CR_Q_dense R2 _ _ abs) as [q [H H0]]. clear abs.
    destruct (CRmorph_rat R1 R2 f q) as [H1 _].
    apply (CRlt_le_trans R2 _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    apply CRopp_gt_lt_contravar in H0.
    destruct (CR_of_Q_opp R2 q) as [H2 _].
    apply (CRlt_le_trans R2 _ _ _ H0) in H2. clear H0.
    pose proof (CRopp_involutive R2 (CRmorph R1 R2 f x)) as [H _].
    apply (CRle_lt_trans R2 _ _ _ H) in H2. clear H.
    destruct (CRmorph_rat R1 R2 f (-q)) as [H _].
    apply (CRlt_le_trans R2 _ _ _ H2) in H. clear H2.
    apply CRmorph_increasing_inv in H.
    destruct (CR_of_Q_opp R1 q) as [_ H2].
    apply (CRlt_le_trans R1 _ _ _ H) in H2. clear H.
    apply CRopp_gt_lt_contravar in H2.
    pose proof (CRopp_involutive R1 (CR_of_Q R1 q)) as [H _].
    apply (CRle_lt_trans R1 _ _ _ H) in H2. clear H.
    exact (CRlt_asym R1 _ _ H1 H2).
  - intro abs.
    destruct (CR_Q_dense R2 _ _ abs) as [q [H H0]]. clear abs.
    destruct (CRmorph_rat R1 R2 f q) as [_ H1].
    apply (CRle_lt_trans R2 _ _ _ H1) in H0. clear H1.
    apply CRmorph_increasing_inv in H0.
    apply CRopp_gt_lt_contravar in H.
    pose proof (CRopp_involutive R2 (CRmorph R1 R2 f x)) as [_ H1].
    apply (CRlt_le_trans R2 _ _ _ H) in H1. clear H.
    destruct (CR_of_Q_opp R2 q) as [_ H2].
    apply (CRle_lt_trans R2 _ _ _ H2) in H1. clear H2.
    destruct (CRmorph_rat R1 R2 f (-q)) as [_ H].
    apply (CRle_lt_trans R2 _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    destruct (CR_of_Q_opp R1 q) as [H2 _].
    apply (CRle_lt_trans R1 _ _ _ H2) in H1. clear H2.
    apply CRopp_gt_lt_contravar in H1.
    pose proof (CRopp_involutive R1 (CR_of_Q R1 q)) as [_ H].
    apply (CRlt_le_trans R1 _ _ _ H1) in H. clear H1.
    exact (CRlt_asym R1 _ _ H0 H).
Qed.

Lemma CRplus_pos_rat_lt : forall (R : ConstructiveReals) (x : CRcarrier R) (q : Q),
    Qlt 0 q -> CRlt R x (CRplus R x (CR_of_Q R q)).
Proof.
  intros.
  apply (CRle_lt_trans R _ (CRplus R x (CRzero R))). apply CRplus_0_r.
  apply CRplus_lt_compat_l.
  apply (CRle_lt_trans R _ (CR_of_Q R 0)). apply CR_of_Q_zero.
  apply CR_of_Q_lt. exact H.
Defined.

Lemma CRplus_neg_rat_lt : forall (R : ConstructiveReals) (x : CRcarrier R) (q : Q),
    Qlt q 0 -> CRlt R (CRplus R x (CR_of_Q R q)) x.
Proof.
  intros.
  apply (CRlt_le_trans R _ (CRplus R x (CRzero R))). 2: apply CRplus_0_r.
  apply CRplus_lt_compat_l.
  apply (CRlt_le_trans R _ (CR_of_Q R 0)).
  apply CR_of_Q_lt. exact H. apply CR_of_Q_zero.
Qed.

Lemma CRmorph_plus_rat : forall (R1 R2 : ConstructiveReals)
                                (f : ConstructiveRealsMorphism R1 R2)
                                (x : CRcarrier R1) (q : Q),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRplus R1 x (CR_of_Q R1 q)))
            (CRplus R2 (CRmorph _ _ f x) (CR_of_Q R2 q)).
Proof.
  split.
  - intro abs.
    destruct (CR_Q_dense R2 _ _ abs) as [r [H H0]]. clear abs.
    destruct (CRmorph_rat _ _ f r) as [H1 _].
    apply (CRlt_le_trans R2 _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    apply (CRlt_asym R1 _ _ H1). clear H1.
    apply (CRplus_lt_reg_r R1 (CRopp R1 (CR_of_Q R1 q))).
    apply (CRlt_le_trans R1 _ x).
    apply (CRle_lt_trans R1 _ (CR_of_Q R1 (r-q))).
    apply (CRle_trans R1 _ (CRplus R1 (CR_of_Q R1 r) (CR_of_Q R1 (-q)))).
    apply CRplus_le_compat_l. destruct (CR_of_Q_opp R1 q). exact H.
    destruct (CR_of_Q_plus R1 r (-q)). exact H.
    apply (CRmorph_increasing_inv _ _ f).
    apply (CRle_lt_trans R2 _ (CR_of_Q R2 (r - q))).
    apply CRmorph_rat.
    apply (CRplus_lt_reg_r R2 (CR_of_Q R2 q)).
    apply (CRle_lt_trans R2 _ (CR_of_Q R2 r)). 2: exact H0.
    intro H.
    destruct (CR_of_Q_plus R2 (r-q) q) as [H1 _].
    apply (CRlt_le_trans R2 _ _ _ H) in H1. clear H.
    apply lt_CR_of_Q in H1. ring_simplify in H1.
    exact (Qlt_not_le _ _ H1 (Qle_refl _)).
    destruct (CRisRing R1).
    apply (CRle_trans R1 _ (CRplus R1 x (CRplus R1 (CR_of_Q R1 q) (CRopp R1 (CR_of_Q R1 q))))).
    apply (CRle_trans R1 _ (CRplus R1 x (CRzero R1))).
    destruct (CRplus_0_r R1 x). exact H.
    apply CRplus_le_compat_l. destruct (Ropp_def (CR_of_Q R1 q)). exact H.
    destruct (Radd_assoc x (CR_of_Q R1 q) (CRopp R1 (CR_of_Q R1 q))).
    exact H1.
  - intro abs.
    destruct (CR_Q_dense R2 _ _ abs) as [r [H H0]]. clear abs.
    destruct (CRmorph_rat _ _ f r) as [_ H1].
    apply (CRle_lt_trans R2 _ _ _ H1) in H0. clear H1.
    apply CRmorph_increasing_inv in H0.
    apply (CRlt_asym R1 _ _ H0). clear H0.
    apply (CRplus_lt_reg_r R1 (CRopp R1 (CR_of_Q R1 q))).
    apply (CRle_lt_trans R1 _ x).
    destruct (CRisRing R1).
    apply (CRle_trans R1 _ (CRplus R1 x (CRplus R1 (CR_of_Q R1 q) (CRopp R1 (CR_of_Q R1 q))))).
    destruct (Radd_assoc x (CR_of_Q R1 q) (CRopp R1 (CR_of_Q R1 q))).
    exact H0.
    apply (CRle_trans R1 _ (CRplus R1 x (CRzero R1))).
    apply CRplus_le_compat_l. destruct (Ropp_def (CR_of_Q R1 q)). exact H1.
    destruct (CRplus_0_r R1 x). exact H1.
    apply (CRlt_le_trans R1 _ (CR_of_Q R1 (r-q))).
    apply (CRmorph_increasing_inv _ _ f).
    apply (CRlt_le_trans R2 _ (CR_of_Q R2 (r - q))).
    apply (CRplus_lt_reg_r R2 (CR_of_Q R2 q)).
    apply (CRlt_le_trans R2 _ _ _ H).
    2: apply CRmorph_rat.
    apply (CRle_trans R2 _ (CR_of_Q R2 (r-q+q))).
    intro abs. apply lt_CR_of_Q in abs. ring_simplify in abs.
    exact (Qlt_not_le _ _ abs (Qle_refl _)).
    destruct (CR_of_Q_plus R2 (r-q) q). exact H1.
    apply (CRle_trans R1 _ (CRplus R1 (CR_of_Q R1 r) (CR_of_Q R1 (-q)))).
    destruct (CR_of_Q_plus R1 r (-q)). exact H1.
    apply CRplus_le_compat_l. destruct (CR_of_Q_opp R1 q). exact H1.
Qed.

Lemma CRmorph_plus : forall (R1 R2 : ConstructiveReals)
                            (f : ConstructiveRealsMorphism R1 R2)
                            (x y : CRcarrier R1),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRplus R1 x y))
            (CRplus R2 (CRmorph _ _ f x) (CRmorph _ _ f y)).
Proof.
  intros R1 R2 f.
  assert (forall (x y : CRcarrier R1),
             orderLe _ (CRlt R2) (CRplus R2 (CRmorph R1 R2 f x) (CRmorph R1 R2 f y))
                     (CRmorph R1 R2 f (CRplus R1 x y))).
  { intros x y abs. destruct (CR_Q_dense R2 _ _ abs) as [r [H H0]]. clear abs.
    destruct (CRmorph_rat _ _ f r) as [H1 _].
    apply (CRlt_le_trans R2 _ _ _ H) in H1. clear H.
    apply CRmorph_increasing_inv in H1.
    apply (CRlt_asym R1 _ _ H1). clear H1.
    destruct (CR_Q_dense R2 _ _ H0) as [q [H2 H3]].
    apply lt_CR_of_Q in H2.
    assert (Qlt (r-q) 0) as epsNeg.
    { apply (Qplus_lt_r _ _ q). ring_simplify. exact H2. }
    destruct (CR_Q_dense R1 _ _ (CRplus_neg_rat_lt R1 x (r-q) epsNeg))
      as [s [H4 H5]].
    apply (CRlt_trans R1 _ (CRplus R1 (CR_of_Q R1 s) y)).
    2: apply CRplus_lt_compat_r, H5.
    apply (CRmorph_increasing_inv _ _ f).
    apply (CRlt_le_trans R2 _ (CRplus R2 (CR_of_Q R2 s) (CRmorph _ _ f y))).
    apply (CRmorph_increasing _ _ f) in H4.
    destruct (CRmorph_plus_rat _ _ f x (r-q)) as [H _].
    apply (CRle_lt_trans R2 _ _ _ H) in H4. clear H.
    destruct (CRmorph_rat _ _ f s) as [_ H1].
    apply (CRlt_le_trans R2 _ _ _ H4) in H1. clear H4.
    apply (CRlt_trans R2 _ (CRplus R2 (CRplus R2 (CRmorph R1 R2 f x) (CR_of_Q R2 (r - q)))
                                   (CRmorph R1 R2 f y))).
    2: apply CRplus_lt_compat_r, H1.
    apply (CRlt_le_trans R2 _ (CRplus R2 (CRplus R2 (CR_of_Q R2 (r - q)) (CRmorph R1 R2 f x))
                                      (CRmorph R1 R2 f y))).
    apply (CRlt_le_trans R2 _ (CRplus R2 (CR_of_Q R2 (r - q))
                                      (CRplus R2 (CRmorph R1 R2 f x) (CRmorph R1 R2 f y)))).
    apply (CRle_lt_trans R2 _ (CRplus R2 (CR_of_Q R2 (r - q)) (CR_of_Q R2 q))).
    2: apply CRplus_lt_compat_l, H3.
    intro abs.
    destruct (CR_of_Q_plus R2 (r-q) q) as [_ H4].
    apply (CRle_lt_trans R2 _ _ _ H4) in abs. clear H4.
    destruct (CRmorph_rat _ _ f r) as [_ H4].
    apply (CRlt_le_trans R2 _ _ _ abs) in H4. clear abs.
    apply lt_CR_of_Q in H4. ring_simplify in H4.
    exact (Qlt_not_le _ _ H4 (Qle_refl _)).
    destruct (CRisRing R2); apply Radd_assoc.
    apply CRplus_le_compat_r. destruct (CRisRing R2).
    destruct (Radd_comm (CRmorph R1 R2 f x) (CR_of_Q R2 (r - q))).
    exact H.
    intro abs.
    destruct (CRmorph_plus_rat _ _ f y s) as [H _]. apply H. clear H.
    apply (CRlt_le_trans R2 _ (CRplus R2 (CR_of_Q R2 s) (CRmorph R1 R2 f y))).
    apply (CRle_lt_trans R2 _ (CRmorph R1 R2 f (CRplus R1 (CR_of_Q R1 s) y))).
    apply CRmorph_proper. destruct (CRisRing R1); apply Radd_comm.
    exact abs. destruct (CRisRing R2); apply Radd_comm. }
  split.
  - apply H.
  - specialize (H (CRplus R1 x y) (CRopp R1 y)).
    intro abs. apply H. clear H.
    apply (CRle_lt_trans R2 _ (CRmorph R1 R2 f x)).
    apply CRmorph_proper. destruct (CRisRing R1).
    apply (CReq_trans R1 _ (CRplus R1 x (CRplus R1 y (CRopp R1 y)))).
    apply CReq_sym, Radd_assoc.
    apply (CReq_trans R1 _ (CRplus R1 x (CRzero R1))). 2: apply CRplus_0_r.
    destruct (CRisRingExt R1). apply Radd_ext.
    apply CReq_refl. apply Ropp_def.
    apply (CRplus_lt_reg_r R2 (CRmorph R1 R2 f y)).
    apply (CRlt_le_trans R2 _ _ _ abs). clear abs.
    apply (CRle_trans R2 _ (CRplus R2 (CRmorph R1 R2 f (CRplus R1 x y)) (CRzero R2))).
    destruct (CRplus_0_r R2 (CRmorph R1 R2 f (CRplus R1 x y))). exact H.
    apply (CRle_trans R2 _ (CRplus R2 (CRmorph R1 R2 f (CRplus R1 x y))
                                   (CRplus R2 (CRmorph R1 R2 f (CRopp R1 y)) (CRmorph R1 R2 f y)))).
    apply CRplus_le_compat_l.
    apply (CRle_trans R2 _ (CRplus R2 (CRopp R2 (CRmorph R1 R2 f y)) (CRmorph R1 R2 f y))).
    destruct (CRplus_opp_l R2 (CRmorph R1 R2 f y)). exact H.
    apply CRplus_le_compat_r. destruct (CRmorph_opp _ _ f y). exact H.
    destruct (CRisRing R2).
    destruct (Radd_assoc (CRmorph R1 R2 f (CRplus R1 x y))
                         (CRmorph R1 R2 f (CRopp R1 y)) (CRmorph R1 R2 f y)).
    exact H0.
Qed.

Lemma CRmorph_mult_pos : forall (R1 R2 : ConstructiveReals)
                           (f : ConstructiveRealsMorphism R1 R2)
                           (x : CRcarrier R1) (n : nat),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRmult R1 x (CR_of_Q R1 (Z.of_nat n # 1))))
            (CRmult R2 (CRmorph _ _ f x) (CR_of_Q R2 (Z.of_nat n # 1))).
Proof.
  induction n.
  - simpl. destruct (CRisRingExt R1).
    apply (CReq_trans R2 _ (CRzero R2)).
    + apply (CReq_trans R2 _ (CRmorph R1 R2 f (CRzero R1))).
      2: apply CRmorph_zero. apply CRmorph_proper.
      apply (CReq_trans R1 _ (CRmult R1 x (CRzero R1))).
      2: apply CRmult_0_r. apply Rmul_ext. apply CReq_refl. apply CR_of_Q_zero.
    + apply (CReq_trans R2 _ (CRmult R2 (CRmorph R1 R2 f x) (CRzero R2))).
      apply CReq_sym, CRmult_0_r. destruct (CRisRingExt R2).
      apply Rmul_ext0. apply CReq_refl. apply CReq_sym, CR_of_Q_zero.
  - destruct (CRisRingExt R1), (CRisRingExt R2).
    apply (CReq_trans
             R2 _  (CRmorph R1 R2 f (CRplus R1 x (CRmult R1 x (CR_of_Q R1 (Z.of_nat n # 1)))))).
    apply CRmorph_proper.
    apply (CReq_trans R1 _ (CRmult R1 x (CRplus R1 (CRone R1) (CR_of_Q R1 (Z.of_nat n # 1))))).
    apply Rmul_ext. apply CReq_refl.
    apply (CReq_trans R1 _ (CR_of_Q R1 (1 + (Z.of_nat n # 1)))).
    apply CR_of_Q_proper. rewrite Nat2Z.inj_succ. unfold Z.succ.
    rewrite Z.add_comm. rewrite Qinv_plus_distr. reflexivity.
    apply (CReq_trans R1 _ (CRplus R1 (CR_of_Q R1 1) (CR_of_Q R1 (Z.of_nat n # 1)))).
    apply CR_of_Q_plus. apply Radd_ext. apply CR_of_Q_one. apply CReq_refl.
    apply (CReq_trans R1 _ (CRplus R1 (CRmult R1 x (CRone R1))
                                   (CRmult R1 x (CR_of_Q R1 (Z.of_nat n # 1))))).
    apply CRmult_plus_distr_l. apply Radd_ext. apply CRmult_1_r. apply CReq_refl.
    apply (CReq_trans R2 _ (CRplus R2 (CRmorph R1 R2 f x)
                                   (CRmorph R1 R2 f (CRmult R1 x (CR_of_Q R1 (Z.of_nat n # 1)))))).
    apply CRmorph_plus.
    apply (CReq_trans R2 _ (CRplus R2 (CRmorph R1 R2 f x)
                                   (CRmult R2 (CRmorph R1 R2 f x) (CR_of_Q R2 (Z.of_nat n # 1))))).
    apply Radd_ext0. apply CReq_refl. exact IHn.
    apply (CReq_trans R2 _ (CRmult R2 (CRmorph R1 R2 f x) (CRplus R2 (CRone R2) (CR_of_Q R2 (Z.of_nat n # 1))))).
    apply (CReq_trans R2 _ (CRplus R2 (CRmult R2 (CRmorph R1 R2 f x) (CRone R2))
                                   (CRmult R2 (CRmorph _ _ f x) (CR_of_Q R2 (Z.of_nat n # 1))))).
    apply Radd_ext0. 2: apply CReq_refl. apply CReq_sym, CRmult_1_r.
    apply CReq_sym, CRmult_plus_distr_l.
    apply Rmul_ext0. apply CReq_refl.
    apply (CReq_trans R2 _ (CR_of_Q R2 (1 + (Z.of_nat n # 1)))).
    apply (CReq_trans R2 _ (CRplus R2 (CR_of_Q R2 1) (CR_of_Q R2 (Z.of_nat n # 1)))).
    apply Radd_ext0. apply CReq_sym, CR_of_Q_one. apply CReq_refl.
    apply CReq_sym, CR_of_Q_plus.
    apply CR_of_Q_proper. rewrite Nat2Z.inj_succ. unfold Z.succ.
    rewrite Z.add_comm. rewrite Qinv_plus_distr. reflexivity.
Qed.

Lemma NatOfZ : forall n : Z, { p : nat | n = Z.of_nat p \/ n = Z.opp (Z.of_nat p) }.
Proof.
  intros [|p|n].
  - exists O. left. reflexivity.
  - exists (Pos.to_nat p). left. rewrite positive_nat_Z. reflexivity.
  - exists (Pos.to_nat n). right. rewrite positive_nat_Z. reflexivity.
Qed.

Lemma CRmorph_mult_int : forall (R1 R2 : ConstructiveReals)
                           (f : ConstructiveRealsMorphism R1 R2)
                           (x : CRcarrier R1) (n : Z),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRmult R1 x (CR_of_Q R1 (n # 1))))
            (CRmult R2 (CRmorph _ _ f x) (CR_of_Q R2 (n # 1))).
Proof.
  intros. destruct (NatOfZ n) as [p [pos|neg]].
  - subst n. apply CRmorph_mult_pos.
  - subst n.
    apply (CReq_trans R2 _ (CRopp R2 (CRmorph R1 R2 f (CRmult R1 x (CR_of_Q R1 (Z.of_nat p # 1)))))).
    + apply (CReq_trans R2 _ (CRmorph R1 R2 f (CRopp R1 (CRmult R1 x (CR_of_Q R1 (Z.of_nat p # 1)))))).
      2: apply CRmorph_opp. apply CRmorph_proper.
      apply (CReq_trans R1 _ (CRmult R1 x (CR_of_Q R1 (- (Z.of_nat p # 1))))).
      destruct (CRisRingExt R1). apply Rmul_ext. apply CReq_refl.
      apply CR_of_Q_proper. reflexivity.
      apply (CReq_trans R1 _ (CRmult R1 x (CRopp R1 (CR_of_Q R1 (Z.of_nat p # 1))))).
      destruct (CRisRingExt R1). apply Rmul_ext. apply CReq_refl.
      apply CR_of_Q_opp. apply CReq_sym, CRopp_mult_distr_r.
    + apply (CReq_trans R2 _ (CRopp R2 (CRmult R2 (CRmorph R1 R2 f x) (CR_of_Q R2 (Z.of_nat p # 1))))).
      destruct (CRisRingExt R2). apply Ropp_ext. apply CRmorph_mult_pos.
      apply (CReq_trans R2 _ (CRmult R2 (CRmorph R1 R2 f x) (CRopp R2 (CR_of_Q R2 (Z.of_nat p # 1))))).
      apply CRopp_mult_distr_r. destruct (CRisRingExt R2).
      apply Rmul_ext. apply CReq_refl.
      apply (CReq_trans R2 _ (CR_of_Q R2 (- (Z.of_nat p # 1)))).
      apply CReq_sym, CR_of_Q_opp. apply CR_of_Q_proper. reflexivity.
Qed.

Lemma CRmorph_mult_inv : forall (R1 R2 : ConstructiveReals)
                           (f : ConstructiveRealsMorphism R1 R2)
                           (x : CRcarrier R1) (p : positive),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRmult R1 x (CR_of_Q R1 (1 # p))))
            (CRmult R2 (CRmorph _ _ f x) (CR_of_Q R2 (1 # p))).
Proof.
  intros. apply (CRmult_eq_reg_r R2 (CR_of_Q R2 (Z.pos p # 1))).
  left. apply (CRle_lt_trans R2 _ (CR_of_Q R2 0)).
  apply CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
  apply (CReq_trans R2 _ (CRmorph _ _ f x)).
  - apply (CReq_trans
             R2 _ (CRmorph R1 R2 f (CRmult R1 (CRmult R1 x (CR_of_Q R1 (1 # p)))
                                           (CR_of_Q R1 (Z.pos p # 1))))).
    apply CReq_sym, CRmorph_mult_int. apply CRmorph_proper.
    apply (CReq_trans
             R1 _ (CRmult R1 x (CRmult R1 (CR_of_Q R1 (1 # p))
                                       (CR_of_Q R1 (Z.pos p # 1))))).
    destruct (CRisRing R1). apply CReq_sym, Rmul_assoc.
    apply (CReq_trans R1 _ (CRmult R1 x (CRone R1))).
    apply (Rmul_ext (CRisRingExt R1)). apply CReq_refl.
    apply (CReq_trans R1 _ (CR_of_Q R1 ((1#p) * (Z.pos p # 1)))).
    apply CReq_sym, CR_of_Q_mult.
    apply (CReq_trans R1 _ (CR_of_Q R1 1)).
    apply CR_of_Q_proper. reflexivity. apply CR_of_Q_one.
    apply CRmult_1_r.
  - apply (CReq_trans R2 _ (CRmult R2 (CRmorph R1 R2 f x)
                                   (CRmult R2 (CR_of_Q R2 (1 # p)) (CR_of_Q R2 (Z.pos p # 1))))).
    2: apply (Rmul_assoc (CRisRing R2)).
    apply (CReq_trans R2 _ (CRmult R2 (CRmorph R1 R2 f x) (CRone R2))).
    apply CReq_sym, CRmult_1_r.
    apply (Rmul_ext (CRisRingExt R2)). apply CReq_refl.
    apply (CReq_trans R2 _ (CR_of_Q R2 1)).
    apply CReq_sym, CR_of_Q_one.
    apply (CReq_trans R2 _ (CR_of_Q R2 ((1#p)*(Z.pos p # 1)))).
    apply CR_of_Q_proper. reflexivity. apply CR_of_Q_mult.
Qed.

Lemma CRmorph_mult_rat : forall (R1 R2 : ConstructiveReals)
                           (f : ConstructiveRealsMorphism R1 R2)
                           (x : CRcarrier R1) (q : Q),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRmult R1 x (CR_of_Q R1 q)))
            (CRmult R2 (CRmorph _ _ f x) (CR_of_Q R2 q)).
Proof.
  intros. destruct q as [a b].
  apply (CReq_trans R2 _ (CRmult R2 (CRmorph _ _ f (CRmult R1 x (CR_of_Q R1 (a # 1))))
                                 (CR_of_Q R2 (1 # b)))).
  - apply (CReq_trans
             R2 _ (CRmorph R1 R2 f (CRmult R1 (CRmult R1 x (CR_of_Q R1 (a # 1)))
                                           (CR_of_Q R1 (1 # b))))).
    2: apply CRmorph_mult_inv. apply CRmorph_proper.
    apply (CReq_trans R1 _ (CRmult R1 x (CRmult R1 (CR_of_Q R1 (a # 1))
                                                (CR_of_Q R1 (1 # b))))).
    apply (Rmul_ext (CRisRingExt R1)). apply CReq_refl.
    apply (CReq_trans R1 _ (CR_of_Q R1 ((a#1)*(1#b)))).
    apply CR_of_Q_proper. unfold Qeq; simpl. rewrite Z.mul_1_r. reflexivity.
    apply CR_of_Q_mult.
    apply (Rmul_assoc (CRisRing R1)).
  - apply (CReq_trans R2 _ (CRmult R2 (CRmult R2 (CRmorph _ _ f x) (CR_of_Q R2 (a # 1)))
                                   (CR_of_Q R2 (1 # b)))).
    apply (Rmul_ext (CRisRingExt R2)). apply CRmorph_mult_int.
    apply CReq_refl.
    apply (CReq_trans R2 _ (CRmult R2 (CRmorph R1 R2 f x)
                                   (CRmult R2 (CR_of_Q R2 (a # 1)) (CR_of_Q R2 (1 # b))))).
    apply CReq_sym, (Rmul_assoc (CRisRing R2)).
    apply (Rmul_ext (CRisRingExt R2)). apply CReq_refl.
    apply (CReq_trans R2 _ (CR_of_Q R2 ((a#1)*(1#b)))).
    apply CReq_sym, CR_of_Q_mult.
    apply CR_of_Q_proper. unfold Qeq; simpl. rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma CRmorph_mult_pos_pos_le : forall (R1 R2 : ConstructiveReals)
                                  (f : ConstructiveRealsMorphism R1 R2)
                                  (x y : CRcarrier R1),
    CRlt R1 (CRzero R1) y
    -> orderLe _ (CRlt R2) (CRmult R2 (CRmorph _ _ f x) (CRmorph _ _ f y))
              (CRmorph _ _ f (CRmult R1 x y)).
Proof.
  intros. intro abs. destruct (CR_Q_dense R2 _ _ abs) as [q [H1 H2]].
  destruct (CRmorph_rat _ _ f q) as [H3 _].
  apply (CRlt_le_trans R2 _ _ _ H1) in H3. clear H1.
  apply CRmorph_increasing_inv in H3.
  apply (CRlt_asym R1 _ _ H3). clear H3.
  destruct (CR_Q_dense R2 _ _ H2) as [r [H1 H3]].
  apply lt_CR_of_Q in H1.
  destruct (CR_archimedean R1 y) as [A Amaj].
  assert (/ ((r - q) * (1 # A)) * (q - r) == - (Z.pos A # 1)) as diveq.
  { rewrite Qinv_mult_distr. setoid_replace (q-r) with (-1*(r-q)).
    field_simplify. reflexivity. 2: field.
    split. intro H4. inversion H4. intro H4.
    apply Qlt_minus_iff in H1. rewrite H4 in H1. inversion H1. }
  destruct (CR_Q_dense R1 (CRplus R1 x (CR_of_Q R1 ((q-r) * (1#A)))) x)
    as [s [H4 H5]].
  - apply (CRlt_le_trans R1 _ (CRplus R1 x (CRzero R1))).
    2: apply CRplus_0_r. apply CRplus_lt_compat_l.
    apply (CRplus_lt_reg_l R1 (CR_of_Q R1 ((r-q) * (1#A)))).
    apply (CRle_lt_trans R1 _ (CRzero R1)).
    apply (CRle_trans R1 _ (CR_of_Q R1 ((r-q)*(1#A) + (q-r)*(1#A)))).
    destruct (CR_of_Q_plus R1 ((r-q)*(1#A)) ((q-r)*(1#A))).
    exact H0. apply (CRle_trans R1 _ (CR_of_Q R1 0)).
    2: destruct (CR_of_Q_zero R1); exact H4.
    intro H4. apply lt_CR_of_Q in H4. ring_simplify in H4.
    inversion H4.
    apply (CRlt_le_trans R1 _ (CR_of_Q R1 ((r - q) * (1 # A)))).
    2: apply CRplus_0_r.
    apply (CRle_lt_trans R1 _ (CR_of_Q R1 0)).
    apply CR_of_Q_zero. apply CR_of_Q_lt.
    rewrite <- (Qmult_0_r (r-q)). apply Qmult_lt_l.
    apply Qlt_minus_iff in H1. exact H1. reflexivity.
  - apply (CRmorph_increasing _ _ f) in H4.
    destruct (CRmorph_plus _ _ f x (CR_of_Q R1 ((q-r) * (1#A)))) as [H6 _].
    apply (CRle_lt_trans R2 _ _ _ H6) in H4. clear H6.
    destruct (CRmorph_rat _ _ f s) as [_ H6].
    apply (CRlt_le_trans R2 _ _ _ H4) in H6. clear H4.
    apply (CRmult_lt_compat_r R2 (CRmorph _ _ f y)) in H6.
    destruct (Rdistr_l (CRisRing R2) (CRmorph _ _ f x)
                       (CRmorph R1 R2 f (CR_of_Q R1 ((q-r) * (1#A))))
                       (CRmorph _ _ f y)) as [H4 _].
    apply (CRle_lt_trans R2 _ _ _ H4) in H6. clear H4.
    apply (CRle_lt_trans R1 _ (CRmult R1 (CR_of_Q R1 s) y)).
    2: apply CRmult_lt_compat_r. 2: exact H. 2: exact H5.
    apply (CRmorph_le_inv _ _ f).
    apply (CRle_trans R2 _ (CR_of_Q R2 q)).
    destruct (CRmorph_rat _ _ f q). exact H4.
    apply (CRle_trans R2 _ (CRmult R2 (CR_of_Q R2 s) (CRmorph _ _ f y))).
    apply (CRle_trans R2 _ (CRplus R2 (CRmult R2 (CRmorph _ _ f x) (CRmorph _ _ f y))
                                   (CR_of_Q R2 (q-r)))).
    apply (CRle_trans R2 _ (CRplus R2 (CR_of_Q R2 r) (CR_of_Q R2 (q - r)))).
    + apply (CRle_trans R2 _ (CR_of_Q R2 (r + (q-r)))).
      intro H4. apply lt_CR_of_Q in H4. ring_simplify in H4.
      exact (Qlt_not_le q q H4 (Qle_refl q)).
      destruct (CR_of_Q_plus R2 r (q-r)). exact H4.
    + apply CRplus_le_compat_r. intro H4.
      apply (CRlt_asym R2 _ _ H3). exact H4.
    + intro H4. apply (CRlt_asym R2 _ _ H4). clear H4.
      apply (CRlt_trans_flip R2 _ _ _ H6). clear H6.
      apply CRplus_lt_compat_l.
      apply (CRlt_le_trans R2 _ (CRmult R2 (CR_of_Q R2 ((q - r) * (1 # A))) (CRmorph R1 R2 f y))).
      apply (CRmult_lt_reg_l R2 (CR_of_Q R2 (/((r-q)*(1#A))))).
      apply (CRle_lt_trans R2 _ (CR_of_Q R2 0)). apply CR_of_Q_zero.
      apply CR_of_Q_lt, Qinv_lt_0_compat.
      rewrite <- (Qmult_0_r (r-q)). apply Qmult_lt_l.
      apply Qlt_minus_iff in H1. exact H1. reflexivity.
      apply (CRle_lt_trans R2 _ (CRopp R2 (CR_of_Q R2 (Z.pos A # 1)))).
      apply (CRle_trans R2 _ (CR_of_Q R2 (-(Z.pos A # 1)))).
      apply (CRle_trans R2 _ (CR_of_Q R2 ((/ ((r - q) * (1 # A))) * (q - r)))).
      destruct (CR_of_Q_mult R2 (/ ((r - q) * (1 # A))) (q - r)).
      exact H0. destruct (CR_of_Q_proper R2 (/ ((r - q) * (1 # A)) * (q - r))
                                         (-(Z.pos A # 1))).
      exact diveq. intro H7. apply lt_CR_of_Q in H7.
      rewrite diveq in H7. exact (Qlt_not_le _ _ H7 (Qle_refl _)).
      destruct (CR_of_Q_opp R2 (Z.pos A # 1)). exact H4.
      apply (CRlt_le_trans R2 _ (CRopp R2 (CRmorph _ _ f y))).
      apply CRopp_gt_lt_contravar.
      apply (CRlt_le_trans R2 _ (CRmorph _ _ f (CR_of_Q R1 (Z.pos A # 1)))).
      apply CRmorph_increasing. exact Amaj.
      destruct (CRmorph_rat _ _ f (Z.pos A # 1)). exact H4.
      apply (CRle_trans R2 _ (CRmult R2 (CRopp R2 (CRone R2)) (CRmorph _ _ f y))).
      apply (CRle_trans R2 _ (CRopp R2 (CRmult R2 (CRone R2) (CRmorph R1 R2 f y)))).
      destruct (Ropp_ext (CRisRingExt R2) (CRmorph _ _ f y)
                         (CRmult R2 (CRone R2) (CRmorph R1 R2 f y))).
      apply CReq_sym, (Rmul_1_l (CRisRing R2)). exact H4.
      destruct (CRopp_mult_distr_l R2 (CRone R2) (CRmorph _ _ f y)). exact H4.
      apply (CRle_trans R2 _ (CRmult R2 (CRmult R2 (CR_of_Q R2 (/ ((r - q) * (1 # A))))
                                                (CR_of_Q R2 ((q - r) * (1 # A))))
                                     (CRmorph R1 R2 f y))).
      apply CRmult_le_compat_r.
      apply (CRle_lt_trans R2 _ (CRmorph _ _ f (CRzero R1))).
      apply CRmorph_zero. apply CRmorph_increasing. exact H.
      apply (CRle_trans R2 _ (CR_of_Q R2 ((/ ((r - q) * (1 # A)))
                                          * ((q - r) * (1 # A))))).
      apply (CRle_trans R2 _ (CR_of_Q R2 (-1))).
      apply (CRle_trans R2 _ (CRopp R2 (CR_of_Q R2 1))).
      destruct (Ropp_ext (CRisRingExt R2) (CRone R2) (CR_of_Q R2 1)).
      apply CReq_sym, CR_of_Q_one. exact H4.
      destruct (CR_of_Q_opp R2 1). exact H0.
      destruct (CR_of_Q_proper R2 (-1) (/ ((r - q) * (1 # A)) * ((q - r) * (1 # A)))).
      field. split.
      intro H4. inversion H4. intro H4. apply Qlt_minus_iff in H1.
      rewrite H4 in H1. inversion H1. exact H4.
      destruct (CR_of_Q_mult R2 (/ ((r - q) * (1 # A))) ((q - r) * (1 # A))).
      exact H4.
      destruct (Rmul_assoc (CRisRing R2) (CR_of_Q R2 (/ ((r - q) * (1 # A))))
                           (CR_of_Q R2 ((q - r) * (1 # A)))
                           (CRmorph R1 R2 f y)).
      exact H0.
      apply CRmult_le_compat_r.
      apply (CRle_lt_trans R2 _ (CRmorph _ _ f (CRzero R1))).
      apply CRmorph_zero. apply CRmorph_increasing. exact H.
      destruct (CRmorph_rat _ _ f ((q - r) * (1 # A))). exact H0.
    + apply (CRle_trans R2 _ (CRmorph _ _ f (CRmult R1 y (CR_of_Q R1 s)))).
      apply (CRle_trans R2 _ (CRmult R2 (CRmorph R1 R2 f y) (CR_of_Q R2 s))).
      destruct (Rmul_comm (CRisRing R2) (CRmorph R1 R2 f y) (CR_of_Q R2 s)).
      exact H0.
      destruct (CRmorph_mult_rat _ _ f y s). exact H0.
      destruct (CRmorph_proper _ _ f (CRmult R1 y (CR_of_Q R1 s))
                               (CRmult R1 (CR_of_Q R1 s) y)).
      apply (Rmul_comm (CRisRing R1)). exact H4.
    + apply (CRle_lt_trans R2 _ (CRmorph _ _ f (CRzero R1))).
      apply CRmorph_zero. apply CRmorph_increasing. exact H.
Qed.

Lemma CRmorph_mult_pos_pos : forall (R1 R2 : ConstructiveReals)
                               (f : ConstructiveRealsMorphism R1 R2)
                               (x y : CRcarrier R1),
    CRlt R1 (CRzero R1) y
    -> orderEq _ (CRlt R2) (CRmorph _ _ f (CRmult R1 x y))
              (CRmult R2 (CRmorph _ _ f x) (CRmorph _ _ f y)).
Proof.
  split. apply CRmorph_mult_pos_pos_le. exact H.
  intro abs. destruct (CR_Q_dense R2 _ _ abs) as [q [H1 H2]].
  destruct (CRmorph_rat _ _ f q) as [_ H3].
  apply (CRle_lt_trans R2 _ _ _ H3) in H2. clear H3.
  apply CRmorph_increasing_inv in H2.
  apply (CRlt_asym R1 _ _ H2). clear H2.
  destruct (CR_Q_dense R2 _ _ H1) as [r [H2 H3]].
  apply lt_CR_of_Q in H3.
  destruct (CR_archimedean R1 y) as [A Amaj].
  destruct (CR_Q_dense R1 x (CRplus R1 x (CR_of_Q R1 ((q-r) * (1#A)))))
    as [s [H4 H5]].
  - apply (CRle_lt_trans R1 _ (CRplus R1 x (CRzero R1))).
    apply CRplus_0_r. apply CRplus_lt_compat_l.
    apply (CRle_lt_trans R1 _ (CR_of_Q R1 0)).
    apply CR_of_Q_zero. apply CR_of_Q_lt.
    rewrite <- (Qmult_0_r (q-r)). apply Qmult_lt_l.
    apply Qlt_minus_iff in H3. exact H3. reflexivity.
  - apply (CRmorph_increasing _ _ f) in H5.
    destruct (CRmorph_plus _ _ f x (CR_of_Q R1 ((q-r) * (1#A)))) as [_ H6].
    apply (CRlt_le_trans R2 _ _ _ H5) in H6. clear H5.
    destruct (CRmorph_rat _ _ f s) as [H5 _ ].
    apply (CRle_lt_trans R2 _ _ _ H5) in H6. clear H5.
    apply (CRmult_lt_compat_r R2 (CRmorph _ _ f y)) in H6.
    apply (CRlt_le_trans R1 _ (CRmult R1 (CR_of_Q R1 s) y)).
    apply CRmult_lt_compat_r. exact H. exact H4. clear H4.
    apply (CRmorph_le_inv _ _ f).
    apply (CRle_trans R2 _ (CR_of_Q R2 q)).
    2: destruct (CRmorph_rat _ _ f q); exact H0.
    apply (CRle_trans R2 _ (CRmult R2 (CR_of_Q R2 s) (CRmorph R1 R2 f y))).
    + apply (CRle_trans R2 _ (CRmorph _ _ f (CRmult R1 y (CR_of_Q R1 s)))).
      destruct (CRmorph_proper _ _ f (CRmult R1 (CR_of_Q R1 s) y)
                               (CRmult R1 y (CR_of_Q R1 s))).
      apply (Rmul_comm (CRisRing R1)). exact H4.
      apply (CRle_trans R2 _ (CRmult R2 (CRmorph R1 R2 f y) (CR_of_Q R2 s))).
      exact (proj2 (CRmorph_mult_rat _ _ f y s)).
      destruct (Rmul_comm (CRisRing R2) (CR_of_Q R2 s) (CRmorph R1 R2 f y)).
      exact H0.
    + intro H5. apply (CRlt_asym R2 _ _ H5). clear H5.
      apply (CRlt_trans R2 _ _ _ H6). clear H6.
      apply (CRle_lt_trans
               R2 _ (CRplus R2
                            (CRmult R2 (CRmorph _ _ f x) (CRmorph _ _ f y))
                            (CRmult R2 (CRmorph R1 R2 f (CR_of_Q R1 ((q - r) * (1 # A))))
                                    (CRmorph R1 R2 f y)))).
      apply (Rdistr_l (CRisRing R2)).
      apply (CRle_lt_trans
               R2 _ (CRplus R2 (CR_of_Q R2 r)
                            (CRmult R2 (CRmorph R1 R2 f (CR_of_Q R1 ((q - r) * (1 # A))))
                                    (CRmorph R1 R2 f y)))).
      apply CRplus_le_compat_r. intro H5. apply (CRlt_asym R2 _ _ H5 H2).
      clear H2.
      apply (CRle_lt_trans
               R2 _ (CRplus R2 (CR_of_Q R2 r)
                            (CRmult R2 (CR_of_Q R2 ((q - r) * (1 # A)))
                                    (CRmorph R1 R2 f y)))).
      apply CRplus_le_compat_l, CRmult_le_compat_r.
      apply (CRle_lt_trans R2 _ (CRmorph _ _ f (CRzero R1))).
      apply CRmorph_zero. apply CRmorph_increasing. exact H.
      destruct (CRmorph_rat _ _ f ((q - r) * (1 # A))). exact H2.
      apply (CRlt_le_trans R2 _ (CRplus R2 (CR_of_Q R2 r)
                                        (CR_of_Q R2 ((q - r))))).
      apply CRplus_lt_compat_l.
      * apply (CRmult_lt_reg_l R2 (CR_of_Q R2 (/((q - r) * (1 # A))))).
        apply (CRle_lt_trans R2 _ (CR_of_Q R2 0)). apply CR_of_Q_zero.
        apply CR_of_Q_lt, Qinv_lt_0_compat.
        rewrite <- (Qmult_0_r (q-r)). apply Qmult_lt_l.
        apply Qlt_minus_iff in H3. exact H3. reflexivity.
        apply (CRle_lt_trans R2 _ (CRmorph _ _ f y)).
        apply (CRle_trans R2 _ (CRmult R2 (CRmult R2 (CR_of_Q R2 (/ ((q - r) * (1 # A))))
                                                  (CR_of_Q R2 ((q - r) * (1 # A))))
                                       (CRmorph R1 R2 f y))).
        exact (proj2 (Rmul_assoc (CRisRing R2) (CR_of_Q R2 (/ ((q - r) * (1 # A))))
                                 (CR_of_Q R2 ((q - r) * (1 # A)))
                                 (CRmorph _ _ f y))).
        apply (CRle_trans R2 _ (CRmult R2 (CRone R2) (CRmorph R1 R2 f y))).
        apply CRmult_le_compat_r.
        apply (CRle_lt_trans R2 _ (CRmorph _ _ f (CRzero R1))).
        apply CRmorph_zero. apply CRmorph_increasing. exact H.
        apply (CRle_trans R2 _ (CR_of_Q R2 ((/ ((q - r) * (1 # A))) * ((q - r) * (1 # A))))).
        exact (proj1 (CR_of_Q_mult R2 (/ ((q - r) * (1 # A))) ((q - r) * (1 # A)))).
        apply (CRle_trans R2 _ (CR_of_Q R2 1)).
        destruct (CR_of_Q_proper R2 (/ ((q - r) * (1 # A)) * ((q - r) * (1 # A))) 1).
        field_simplify. reflexivity. split.
        intro H5. inversion H5. intro H5. apply Qlt_minus_iff in H3.
        rewrite H5 in H3. inversion H3. exact H2.
        destruct (CR_of_Q_one R2). exact H2.
        destruct (Rmul_1_l (CRisRing R2) (CRmorph _ _ f y)).
        intro H5. contradiction.
        apply (CRlt_le_trans R2 _ (CR_of_Q R2 (Z.pos A # 1))).
        apply (CRlt_le_trans R2 _ (CRmorph _ _ f (CR_of_Q R1 (Z.pos A # 1)))).
        apply CRmorph_increasing. exact Amaj.
        exact (proj2 (CRmorph_rat _ _ f (Z.pos A # 1))).
        apply (CRle_trans R2 _ (CR_of_Q R2 ((/ ((q - r) * (1 # A))) * (q - r)))).
        2: exact (proj2 (CR_of_Q_mult R2 (/ ((q - r) * (1 # A))) (q - r))).
        destruct (CR_of_Q_proper R2 (Z.pos A # 1) (/ ((q - r) * (1 # A)) * (q - r))).
        field_simplify. reflexivity. split.
        intro H5. inversion H5. intro H5. apply Qlt_minus_iff in H3.
        rewrite H5 in H3. inversion H3. exact H2.
      * apply (CRle_trans R2 _ (CR_of_Q R2 (r + (q-r)))).
        exact (proj1 (CR_of_Q_plus R2 r (q-r))).
        destruct (CR_of_Q_proper R2 (r + (q-r)) q). ring. exact H2.
    + apply (CRle_lt_trans R2 _ (CRmorph _ _ f (CRzero R1))).
      apply CRmorph_zero. apply CRmorph_increasing. exact H.
Qed.

Lemma CRmorph_mult : forall (R1 R2 : ConstructiveReals)
                       (f : ConstructiveRealsMorphism R1 R2)
                       (x y : CRcarrier R1),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRmult R1 x y))
            (CRmult R2 (CRmorph _ _ f x) (CRmorph _ _ f y)).
Proof.
  intros.
  destruct (CR_archimedean R1 (CRopp R1 y)) as [p pmaj].
  apply (CRplus_eq_reg_r R2 (CRmult R2 (CRmorph _ _ f x)
                                    (CR_of_Q R2 (Z.pos p # 1)))).
  apply (CReq_trans R2 _ (CRmorph _ _ f (CRmult R1 x (CRplus R1 y (CR_of_Q R1 (Z.pos p # 1)))))).
  - apply (CReq_trans R2 _ (CRplus R2 (CRmorph R1 R2 f (CRmult R1 x y))
                                   (CRmorph R1 R2 f (CRmult R1 x (CR_of_Q R1 (Z.pos p # 1)))))).
    apply (Radd_ext (CRisRingExt R2)). apply CReq_refl.
    apply CReq_sym, CRmorph_mult_int.
    apply (CReq_trans R2 _ (CRmorph _ _ f (CRplus R1 (CRmult R1 x y)
                                                  (CRmult R1 x (CR_of_Q R1 (Z.pos p # 1)))))).
    apply CReq_sym, CRmorph_plus. apply CRmorph_proper.
    apply CReq_sym, CRmult_plus_distr_l.
  - apply (CReq_trans R2 _ (CRmult R2 (CRmorph _ _ f x)
                                   (CRmorph _ _ f (CRplus R1 y (CR_of_Q R1 (Z.pos p # 1)))))).
    apply CRmorph_mult_pos_pos.
    apply (CRplus_lt_compat_l R1 y) in pmaj.
    apply (CRle_lt_trans R1 _ (CRplus R1 y (CRopp R1 y))).
    2: exact pmaj. apply (CRisRing R1).
    apply (CReq_trans R2 _ (CRmult R2 (CRmorph R1 R2 f x)
                                 (CRplus R2 (CRmorph R1 R2 f y) (CR_of_Q R2 (Z.pos p # 1))))).
    apply (Rmul_ext (CRisRingExt R2)). apply CReq_refl.
    apply (CReq_trans R2 _ (CRplus R2 (CRmorph R1 R2 f y)
                                 (CRmorph _ _ f (CR_of_Q R1 (Z.pos p # 1))))).
    apply CRmorph_plus.
    apply (Radd_ext (CRisRingExt R2)). apply CReq_refl.
    apply CRmorph_rat.
    apply CRmult_plus_distr_l.
Qed.

Lemma CRmorph_appart : forall (R1 R2 : ConstructiveReals)
                         (f : ConstructiveRealsMorphism R1 R2)
                         (x y : CRcarrier R1)
                         (app : orderAppart _ (CRlt R1) x y),
    orderAppart _ (CRlt R2) (CRmorph _ _ f x) (CRmorph _ _ f y).
Proof.
  intros. destruct app.
  - left. apply CRmorph_increasing. exact c.
  - right. apply CRmorph_increasing. exact c.
Defined.

Lemma CRmorph_appart_zero : forall (R1 R2 : ConstructiveReals)
                              (f : ConstructiveRealsMorphism R1 R2)
                              (x : CRcarrier R1)
                              (app : orderAppart _ (CRlt R1) x (CRzero R1)),
    orderAppart _ (CRlt R2) (CRmorph _ _ f x) (CRzero R2).
Proof.
  intros. destruct app.
  - left. apply (CRlt_le_trans R2 _ (CRmorph _ _ f (CRzero R1))).
    apply CRmorph_increasing. exact c.
    exact (proj2 (CRmorph_zero _ _ f)).
  - right. apply (CRle_lt_trans R2 _ (CRmorph _ _ f (CRzero R1))).
    exact (proj1 (CRmorph_zero _ _ f)).
    apply CRmorph_increasing. exact c.
Defined.

Lemma CRmorph_inv : forall (R1 R2 : ConstructiveReals)
                      (f : ConstructiveRealsMorphism R1 R2)
                      (x : CRcarrier R1)
                      (xnz : orderAppart _ (CRlt R1) x (CRzero R1))
                      (fxnz : orderAppart _ (CRlt R2) (CRmorph _ _ f x) (CRzero R2)),
    orderEq _ (CRlt R2) (CRmorph _ _ f (CRinv R1 x xnz))
            (CRinv R2 (CRmorph _ _ f x) fxnz).
Proof.
  intros. apply (CRmult_eq_reg_r R2 (CRmorph _ _ f x)).
  destruct fxnz. right. exact c. left. exact c.
  apply (CReq_trans R2 _ (CRone R2)).
  2: apply CReq_sym, CRinv_l.
  apply (CReq_trans R2 _ (CRmorph _ _ f (CRmult R1 (CRinv R1 x xnz) x))).
  apply CReq_sym, CRmorph_mult.
  apply (CReq_trans R2 _ (CRmorph _ _ f (CRone R1))).
  apply CRmorph_proper. apply CRinv_l.
  apply CRmorph_one.
Qed.

Definition CauchyMorph (R : ConstructiveReals)
  : CReal -> CRcarrier R.
Proof.
  intros [xn xcau].
  destruct (CR_complete R (fun n:nat => CR_of_Q R (xn n))).
  - intros p. exists (Pos.to_nat p). intros.
    specialize (xcau p i j H H0). apply Qlt_le_weak in xcau.
    rewrite Qabs_Qle_condition in xcau. split.
    + unfold CRminus.
      apply (CRle_trans R _ (CRplus R (CR_of_Q R (xn i)) (CR_of_Q R (-xn j)))).
      apply (CRle_trans R _ (CR_of_Q R (xn i-xn j))).
      apply CR_of_Q_le. apply xcau. exact (proj2 (CR_of_Q_plus R _ _)).
      apply CRplus_le_compat_l. exact (proj2 (CR_of_Q_opp R (xn j))).
    + unfold CRminus.
      apply (CRle_trans R _ (CRplus R (CR_of_Q R (xn i)) (CR_of_Q R (-xn j)))).
      apply CRplus_le_compat_l. exact (proj1 (CR_of_Q_opp R (xn j))).
      apply (CRle_trans R _ (CR_of_Q R (xn i-xn j))).
      exact (proj1 (CR_of_Q_plus R _ _)).
      apply CR_of_Q_le. apply xcau.
  - exact x.
Defined.

Lemma CauchyMorph_rat : forall (R : ConstructiveReals) (q : Q),
    orderEq _ (CRlt R) (CauchyMorph R (inject_Q q)) (CR_of_Q R q).
Proof.
  intros.
  unfold CauchyMorph; simpl;
    destruct (CRltLinear R), p, (CR_complete R (fun _ : nat => CR_of_Q R q)).
  apply CR_cv_const in c0. apply CReq_sym. exact c0.
Qed.

Lemma CauchyMorph_increasing_Ql : forall (R : ConstructiveReals) (x : CReal) (q : Q),
    CRealLt x (inject_Q q) -> CRlt R (CauchyMorph R x) (CR_of_Q R q).
Proof.
  intros.
  unfold CauchyMorph; simpl;
    destruct x as [xn xcau], (CRltLinear R), p, (CR_complete R (fun n : nat => CR_of_Q R (xn n))).
  destruct (CRealQ_dense _ _ H) as [r [H0 H1]].
  apply lt_inject_Q in H1.
  destruct (s _ x _ (CR_of_Q_lt R _ _ H1)). 2: exact c1. exfalso.
  clear H1 H q.
  (* For an index high enough, xn should be both higher
     and lower than r, which is absurd. *)
  apply CRealLt_above in H0.
  destruct H0 as [p pmaj]. simpl in pmaj.
  destruct (CR_cv_above_rat R xn x r c0 c1).
  assert (x0 <= Nat.max (Pos.to_nat p) (S x0))%nat.
  { apply (le_trans _ (S x0)). apply le_S, le_refl. apply Nat.le_max_r. }
  specialize (q (Nat.max (Pos.to_nat p) (S x0)) H). clear H.
  specialize (pmaj (Pos.max p (Pos.of_nat (S x0))) (Pos.le_max_l _ _)).
  rewrite Pos2Nat.inj_max, Nat2Pos.id in pmaj. 2: discriminate.
  apply (Qlt_not_le _ _ q). apply Qlt_le_weak.
  apply Qlt_minus_iff. apply (Qlt_trans _ (2#p)). reflexivity. exact pmaj.
Qed.

Lemma CauchyMorph_increasing_Qr : forall (R : ConstructiveReals) (x : CReal) (q : Q),
    CRealLt (inject_Q q) x -> CRlt R (CR_of_Q R q) (CauchyMorph R x).
Proof.
  intros.
  unfold CauchyMorph; simpl;
    destruct x as [xn xcau], (CRltLinear R), p, (CR_complete R (fun n : nat => CR_of_Q R (xn n))).
  destruct (CRealQ_dense _ _ H) as [r [H0 H1]].
  apply lt_inject_Q in H0.
  destruct (s _ x _ (CR_of_Q_lt R _ _ H0)). exact c1. exfalso.
  clear H0 H q.
  (* For an index high enough, xn should be both higher
     and lower than r, which is absurd. *)
  apply CRealLt_above in H1.
  destruct H1 as [p pmaj]. simpl in pmaj.
  destruct (CR_cv_below_rat R xn x r c0 c1).
  assert (x0 <= Nat.max (Pos.to_nat p) (S x0))%nat.
  { apply (le_trans _ (S x0)). apply le_S, le_refl. apply Nat.le_max_r. }
  specialize (q (Nat.max (Pos.to_nat p) (S x0)) H). clear H.
  specialize (pmaj (Pos.max p (Pos.of_nat (S x0))) (Pos.le_max_l _ _)).
  rewrite Pos2Nat.inj_max, Nat2Pos.id in pmaj. 2: discriminate.
  apply (Qlt_not_le _ _ q). apply Qlt_le_weak.
  apply Qlt_minus_iff. apply (Qlt_trans _ (2#p)). reflexivity. exact pmaj.
Qed.

Lemma CauchyMorph_increasing : forall (R : ConstructiveReals) (x y : CReal),
    CRealLt x y -> CRlt R (CauchyMorph R x) (CauchyMorph R y).
Proof.
  intros.
  destruct (CRealQ_dense _ _ H) as [q [H0 H1]].
  apply (CRlt_trans R _ (CR_of_Q R q)).
  apply CauchyMorph_increasing_Ql. exact H0.
  apply CauchyMorph_increasing_Qr. exact H1.
Qed.

Definition CauchyMorphism (R : ConstructiveReals) : ConstructiveRealsMorphism CRealImplem R.
Proof.
  apply (Build_ConstructiveRealsMorphism CRealImplem R (CauchyMorph R)).
  exact (CauchyMorph_rat R).
  exact (CauchyMorph_increasing R).
Defined.

Lemma RightBound : forall (R : ConstructiveReals) (x : CRcarrier R) (p q r : Q),
    CRlt R x (CR_of_Q R q)
    -> CRlt R x (CR_of_Q R r)
    -> CRlt R (CR_of_Q R q) (CRplus R x (CR_of_Q R p))
    -> CRlt R (CR_of_Q R r) (CRplus R x (CR_of_Q R p))
    -> Qlt (Qabs (q - r)) p.
Proof.
  intros. apply Qabs_case.
  - intros. apply (Qplus_lt_l _ _ r). ring_simplify.
    apply (lt_CR_of_Q R), (CRlt_le_trans R _ _ _ H1).
    apply (CRle_trans R _ (CRplus R (CR_of_Q R r) (CR_of_Q R p))).
    intro abs. apply CRplus_lt_reg_r in abs.
    exact (CRlt_asym R _ _ abs H0).
    destruct (CR_of_Q_plus R r p). exact H4.
  - intros. apply (Qplus_lt_l _ _ q). ring_simplify.
    apply (lt_CR_of_Q R), (CRlt_le_trans R _ _ _ H2).
    apply (CRle_trans R _ (CRplus R (CR_of_Q R q) (CR_of_Q R p))).
    intro abs. apply CRplus_lt_reg_r in abs.
    exact (CRlt_asym R _ _ abs H).
    destruct (CR_of_Q_plus R q p). exact H4.
Qed.

Definition CauchyMorph_inv (R : ConstructiveReals)
  : CRcarrier R -> CReal.
Proof.
  intro x.
  exists (fun n:nat => let (q,_) := CR_Q_dense
                            R x _ (CRplus_pos_rat_lt R x (1 # Pos.of_nat (S n)) (eq_refl _))
             in q).
  intros n p q H0 H1.
  destruct (CR_Q_dense R x (CRplus R x (CR_of_Q R (1 # Pos.of_nat (S p))))
                       (CRplus_pos_rat_lt R x (1 # Pos.of_nat (S p)) (eq_refl _)))
    as [r [H2 H3]].
  destruct (CR_Q_dense R x (CRplus R x (CR_of_Q R (1 # Pos.of_nat (S q))))
                       (CRplus_pos_rat_lt R x (1 # Pos.of_nat (S q)) (eq_refl _)))
    as [s [H4 H5]].
  apply (RightBound R x (1#n) r s). exact H2. exact H4.
  apply (CRlt_trans R _ _ _ H3), CRplus_lt_compat_l, CR_of_Q_lt.
  unfold Qlt. do 2 rewrite Z.mul_1_l. unfold Qden.
  apply Pos2Z.pos_lt_pos, Pos2Nat.inj_lt. rewrite Nat2Pos.id.
  2: discriminate. apply le_n_S. exact H0.
  apply (CRlt_trans R _ _ _ H5), CRplus_lt_compat_l, CR_of_Q_lt.
  unfold Qlt. do 2 rewrite Z.mul_1_l. unfold Qden.
  apply Pos2Z.pos_lt_pos, Pos2Nat.inj_lt. rewrite Nat2Pos.id.
  2: discriminate. apply le_n_S. exact H1.
Defined.

Lemma CauchyMorph_inv_rat : forall (R : ConstructiveReals) (q : Q),
    CRealEq (CauchyMorph_inv R (CR_of_Q R q)) (inject_Q q).
Proof.
  split.
  - intros [n nmaj]. unfold CauchyMorph_inv, proj1_sig, inject_Q in nmaj.
    destruct (CR_Q_dense R (CR_of_Q R q)
                         (CRplus R (CR_of_Q R q) (CR_of_Q R (1 # Pos.of_nat (S (Pos.to_nat n)))))
                         (CRplus_pos_rat_lt R (CR_of_Q R q) (1 # Pos.of_nat (S (Pos.to_nat n)))
                                            eq_refl))
      as [r [H _]].
    apply lt_CR_of_Q, Qlt_minus_iff in H.
    apply (Qlt_not_le _ _ H), (Qplus_le_l _ _ (q-r)).
    ring_simplify. apply (Qle_trans _ (2#n)). discriminate.
    apply Qlt_le_weak. ring_simplify in nmaj. rewrite Qplus_comm. exact nmaj.
  - intros [n nmaj]. unfold CauchyMorph_inv, proj1_sig, inject_Q in nmaj.
    destruct (CR_Q_dense R (CR_of_Q R q)
                         (CRplus R (CR_of_Q R q) (CR_of_Q R (1 # Pos.of_nat (S (Pos.to_nat n)))))
                         (CRplus_pos_rat_lt R (CR_of_Q R q) (1 # Pos.of_nat (S (Pos.to_nat n)))
                                            eq_refl))
      as [r [_ H0]].
    destruct (CR_of_Q_plus R q (1 # Pos.of_nat (S (Pos.to_nat n)))) as [H1 _].
    apply (CRlt_le_trans R _ _ _ H0) in H1. clear H0.
    apply lt_CR_of_Q, (Qplus_lt_l _ _ (-q)) in H1.
    ring_simplify in H1. ring_simplify in nmaj.
    apply (Qlt_trans _ _ _ nmaj) in H1. clear nmaj.
    apply (Qlt_not_le _ _ H1). clear H1.
    apply (Qle_trans _ (1#n)).
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. 2: discriminate. apply le_S, le_refl.
    unfold Qle, Qnum, Qden. apply Z.mul_le_mono_nonneg_r.
    2: discriminate. apply Pos2Z.pos_is_nonneg.
Qed.

(* The easier side, because CauchyMorph_inv takes a limit from above. *)
Lemma CauchyMorph_inv_increasing_Qr
  : forall (R : ConstructiveReals) (x : CRcarrier R) (q : Q),
    CRlt R (CR_of_Q R q) x -> CRealLt (inject_Q q) (CauchyMorph_inv R x).
Proof.
  intros.
  destruct (CR_Q_dense R _ _ H) as [r [H2 H3]].
  apply lt_CR_of_Q in H2.
  destruct (Qarchimedean (/(r-q))) as [p pmaj].
  exists (2*p)%positive. unfold CauchyMorph_inv, inject_Q, proj1_sig.
  destruct (CR_Q_dense
              R x (CRplus R x (CR_of_Q R (1 # Pos.of_nat (S (Pos.to_nat (2*p))))))
              (CRplus_pos_rat_lt R x (1 # Pos.of_nat (S (Pos.to_nat (2*p)))) eq_refl))
    as [t [H4 H5]].
  setoid_replace (2#2*p) with (1#p). 2: reflexivity.
  apply (Qlt_trans _ (r-q)).
  apply (Qmult_lt_l _ _ (r-q)) in pmaj.
  rewrite Qmult_inv_r in pmaj.
  apply Qlt_shift_inv_r in pmaj. 2: reflexivity. exact pmaj.
  intro abs. apply Qlt_minus_iff in H2.
  rewrite abs in H2. inversion H2.
  apply Qlt_minus_iff in H2. exact H2.
  apply Qplus_lt_l, (lt_CR_of_Q R), (CRlt_trans R _ x _ H3 H4).
Qed.

Lemma CauchyMorph_inv_increasing : forall (R : ConstructiveReals) (x y : CRcarrier R),
    CRlt R x y -> CRealLt (CauchyMorph_inv R x) (CauchyMorph_inv R y).
Proof.
  intros.
  destruct (CR_Q_dense R _ _ H) as [q [H0 H1]].
  apply (CReal_lt_trans _ (inject_Q q)).
  - clear H1 H y.
    destruct (CR_Q_dense R _ _ H0) as [r [H2 H3]].
    apply lt_CR_of_Q in H3.
    destruct (Qarchimedean (/(q-r))) as [p pmaj].
    exists (4*p)%positive. unfold CauchyMorph_inv, inject_Q, proj1_sig.
    destruct (CR_Q_dense
                R x (CRplus R x (CR_of_Q R (1 # Pos.of_nat (S (Pos.to_nat (4*p))))))
                (CRplus_pos_rat_lt R x (1 # Pos.of_nat (S (Pos.to_nat (4*p)))) eq_refl))
      as [t [H4 H5]].
    setoid_replace (2#4*p) with (1#2*p). 2: reflexivity.
    assert (1 # 2 * p < (q - r) / 2) as H.
    { apply Qlt_shift_div_l. reflexivity.
      setoid_replace ((1#2*p)*2) with (1#p).
      apply (Qmult_lt_l _ _ (q-r)) in pmaj.
      rewrite Qmult_inv_r in pmaj.
      apply Qlt_shift_inv_r in pmaj. 2: reflexivity. exact pmaj.
      intro abs. apply Qlt_minus_iff in H3.
      rewrite abs in H3. inversion H3.
      apply Qlt_minus_iff in H3. exact H3.
      rewrite Qmult_comm. reflexivity. }
    apply (Qlt_trans _ ((q-r)/2)). exact H.
    apply (Qplus_lt_l _ _ (t + (r-q)/2)). field_simplify.
    setoid_replace (2*t/2) with t. 2: field.
    apply (lt_CR_of_Q R). apply (CRlt_trans R _ _ _ H5).
    apply (CRlt_trans
             R _ (CRplus R (CR_of_Q R r) (CR_of_Q R (1 # Pos.of_nat (S (Pos.to_nat (4 * p))))))).
    apply CRplus_lt_compat_r. exact H2.
    apply (CRle_lt_trans
             R _ (CR_of_Q R (r + (1 # Pos.of_nat (S (Pos.to_nat (4 * p))))))).
    apply CR_of_Q_plus. apply CR_of_Q_lt.
    apply (Qlt_le_trans _ (r + (q-r)/2)).
    2: field_simplify; apply Qle_refl.
    apply Qplus_lt_r.
    apply (Qlt_trans _ (1#2*p)). 2: exact H.
    unfold Qlt. do 2 rewrite Z.mul_1_l. unfold Qden.
    apply Pos2Z.pos_lt_pos.
    rewrite Nat2Pos.inj_succ, Pos2Nat.id.
    apply (Pos.lt_trans _ (4*p)). apply Pos2Nat.inj_lt.
    do 2 rewrite Pos2Nat.inj_mul.
    apply Nat.mul_lt_mono_pos_r. apply Pos2Nat.is_pos.
    unfold Pos.to_nat. simpl. auto.
    apply Pos.lt_succ_diag_r.
    intro abs. pose proof (Pos2Nat.is_pos (4*p)).
    rewrite abs in H1. inversion H1.
  - apply CauchyMorph_inv_increasing_Qr. exact H1.
Qed.

Definition CauchyMorphismInv (R : ConstructiveReals)
  : ConstructiveRealsMorphism R CRealImplem.
Proof.
  apply (Build_ConstructiveRealsMorphism R CRealImplem (CauchyMorph_inv R)).
  - apply CauchyMorph_inv_rat.
  - apply CauchyMorph_inv_increasing.
Defined.

Lemma CauchyMorph_surject : forall (R : ConstructiveReals) (x : CRcarrier R),
    orderEq _ (CRlt R) (CauchyMorph R (CauchyMorph_inv R x)) x.
Proof.
  intros.
  apply (Endomorph_id
           R (CRmorph_compose _ _ _ (CauchyMorphismInv R) (CauchyMorphism R)) x).
Qed.

Lemma CauchyMorph_inject : forall (R : ConstructiveReals) (x : CReal),
    CRealEq (CauchyMorph_inv R (CauchyMorph R x)) x.
Proof.
  intros.
  apply (Endomorph_id CRealImplem (CRmorph_compose _ _ _ (CauchyMorphism R) (CauchyMorphismInv R)) x).
Qed.

(* We call this morphism slow to remind that it should only be used
   for proofs, not for computations. *)
Definition SlowConstructiveRealsMorphism (R1 R2 : ConstructiveReals)
  : ConstructiveRealsMorphism R1 R2
  := CRmorph_compose R1 CRealImplem R2
                     (CauchyMorphismInv R1) (CauchyMorphism R2).
