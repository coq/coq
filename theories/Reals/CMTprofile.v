(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Proof that for an integrable function f, the inverse image of
    of most intervals [t, +\infty[ are integrable, when 0 < t.
    As a quick justification : if those inverse images has infinite
    measure, it would be an infinite-area rectangle lower bounding
    the integral of f.

    The difficulty is making this argument constructive. First, we
    approximate the indicator function of [t, +\infty[ by a
    piecewise-linear function that continuously increases from 0 to 1,
    between s < t and t. This means considering the integrable functions
    (min(f,t) - min(f,s)) / (t-s)
    and using the monotone convergence theorem in the limit where s tends
    to t from below. The last, and main, difficulty is to constructively
    prove that this non-increasing limit of integrals exists.
 *)

Require Import QArith_base Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveSum.
Require Import ConstructiveAbs.
Require Import ConstructiveLimits.
Require Import ConstructiveUniformCont.
Require Import ConstructivePartialFunctions.
Require Import ConstructiveDiagonal.
Require Import CMTbase.
Require Import CMTIntegrableFunctions.
Require Import CMTIntegrableSets.
Require Import CMTFullSets.
Require Import CMTReals.

Local Open Scope ConstructiveReals.

Lemma RealSequenceCoverMeasure
  : forall {R : ConstructiveReals}
      (un : nat -> CRcarrier R) (N : nat),
    { coverInt : @IntegrableSet IntSpaceCSUCFunctions
                                (fun x => exists n:nat,
                                     CRltProp R (un n - CRpow (CR_of_Q R (1#2)) (2 + N + n)) x /\
                                     CRltProp R x (un n + CRpow (CR_of_Q R (1#2)) (2 + N + n)))
                 & MeasureSet coverInt <= CRpow (CR_of_Q R (1#2)) N }.
Proof.
  intros.
  assert (forall n:nat, un n - CRpow (CR_of_Q R (1#2)) (2 + N + n)
                 < un n + CRpow (CR_of_Q R (1#2)) (2 + N + n)).
  { intro n. apply CRplus_lt_compat_l.
    apply (CRle_lt_trans _ 0). rewrite <- CRopp_0. apply CRopp_ge_le_contravar.
    apply pow_le, CRlt_asym, CR_of_Q_pos. reflexivity.
    apply pow_lt, CR_of_Q_pos. reflexivity. }
  pose (fun n:nat => OpenIntervalIntegrable _ _ (H n)) as openInt.
  destruct (@IntegrableSetCountableUnionLe
              IntSpaceCSUCFunctions
              (fun n x =>
                 CRltProp R (un n - CRpow (CR_of_Q _ (1#2)) (2 + N + n)) x
                 /\ CRltProp R x (un n + CRpow (CR_of_Q _ (1#2)) (2 + N + n)))
              (fun n => let (i,_) := openInt n in i)
              (CRpow (CR_of_Q R (1#2)) N)).
  - apply (series_cv_eq (fun n => CRpow (CR_of_Q R (1#2)) n
                               * CRpow (CR_of_Q R (1#2)) (S N))).
    intro n. destruct (openInt n). rewrite c.
    unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive.
    rewrite (CRplus_comm (un n)), CRplus_assoc, <- (CRplus_assoc (un n)).
    rewrite CRplus_opp_r, CRplus_0_l.
    rewrite pow_plus_distr, Nat.add_comm. simpl.
    rewrite <- CRmult_plus_distr_r, <- CR_of_Q_plus, Qinv_plus_distr.
    setoid_replace (1 + 1 # 2)%Q with 1%Q. 2: reflexivity.
    rewrite CR_of_Q_one, CRmult_1_l. reflexivity.
    apply (CR_cv_proper _ (CR_of_Q R 2 * CRpow (CR_of_Q R (1 # 2)) (S N))).
    apply series_cv_scale. apply GeoHalfTwo. simpl.
    rewrite <- CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace (2 * (1 # 2))%Q with 1%Q. 2: reflexivity.
    rewrite CR_of_Q_one, CRmult_1_l. reflexivity.
  - exists x. exact c.
Qed.

(* Constructive proof that the computable Cauchy reals are uncountable.
   We prove the even stronger contrapositive : an automatic extraction
   of a real number appart from the image of any real sequence. *)
Lemma CRuncountable
  : forall {R : ConstructiveReals}
      (un : nat -> CRcarrier R) (a b : CRcarrier R),
    a < b
    -> { x : CRcarrier R
            & prod (a < x < b)
                   (forall n:nat, CRapart R x (un n)) }.
Proof.
  intros. pose proof (CRlt_minus a b H).
  destruct (CR_cv_open_above (fun n:nat => CRpow (CR_of_Q R (1#2)) n) (b-a) 0)
    as [n nmaj].
  apply GeoCvZero. exact H0.
  destruct (fun n:nat => OpenIntervalIntegrable a b H)
    as [intervInt intervMes].
  destruct (RealSequenceCoverMeasure un n) as [coverInt coverMes].
  specialize (nmaj n (le_refl n)).
  assert (0 < MeasureSet (IntegrableSetDifference _ _ intervInt coverInt)).
  { rewrite MeasureDifference. apply CRlt_minus.
    apply (CRle_lt_trans _ (MeasureSet coverInt)).
    apply IntegralNonDecreasing. intros x xdf xdg. simpl.
    destruct xdf, xdg. apply CRle_refl. 3: apply CRle_refl.
    2: apply CRlt_asym, CRzero_lt_one. destruct a0. contradiction.
    apply (CRle_lt_trans _ _ _ coverMes). rewrite intervMes. exact nmaj. }
  apply PositiveMeasureInhabited in H1. destruct H1 as [x xcv].
  exists x. destruct xcv, H1. split. split.
  apply CRltEpsilon, H1. apply CRltEpsilon, H3.
  intro k. destruct (CRltLinear R).
  destruct (s (un k - CRpow (CR_of_Q R (1 # 2)) (2 + n + k)) x (un k)).
  3: left; exact c.
  - apply (CRplus_lt_reg_r (CRpow (CR_of_Q R (1 # 2)) (2 + n + k))).
    unfold CRminus. rewrite CRplus_assoc. apply CRplus_lt_compat_l.
    rewrite CRplus_opp_l. apply pow_lt, CR_of_Q_pos. reflexivity.
  - destruct (s (un k) x (un k + CRpow (CR_of_Q R (1 # 2)) (2 + n + k))).
    + apply (CRle_lt_trans _ (un k + 0)). rewrite CRplus_0_r. apply CRle_refl.
      apply CRplus_lt_compat_l. apply pow_lt, CR_of_Q_pos. reflexivity.
    + right. exact c0.
    + exfalso. apply H2. exists k. split.
      apply CRltForget. exact c. apply CRltForget. exact c0.
Qed.

Lemma CRuncountableDiag
  : forall {R : ConstructiveReals}
      (un : nat -> nat -> CRcarrier R) (a b : CRcarrier R),
    a < b
    -> { x : CRcarrier R
            & prod (a < x < b)
                   (forall n k:nat, CRapart R x (un n k)) }.
Proof.
  intros.
  destruct (CRuncountable (fun p:nat => let (n, k) := diagPlaneInv p in un n k)
                          a b H).
  exists x. split. exact (fst p). intros n k.
  destruct p. specialize (c (diagPlane n k)).
  rewrite diagPlaneInject in c. exact c.
Qed.

Lemma CRuncountableDiag3
  : forall {R : ConstructiveReals}
      (un : nat -> nat -> nat -> CRcarrier R) (a b : CRcarrier R),
    a < b
    -> { x : CRcarrier R
            & prod (a < x < b)
                   (forall n k i:nat, CRapart R x (un n k i)) }.
Proof.
  intros.
  destruct (CRuncountableDiag
              (fun p i:nat => let (n, k) := diagPlaneInv p in un n k i)
              a b H).
  exists x. split. exact (fst p). intros n k i.
  destruct p. specialize (c (diagPlane n k) i).
  rewrite diagPlaneInject in c. exact c.
Qed.



Definition StepApprox {R : ConstructiveReals} {X : Set}
           (f : PartialFunction X)
           (s t : CRcarrier R) (ltst : s < t) : PartialFunction X
  := Xscale (CRinv R (t - s) (inr (CRlt_minus s t ltst)))
            (Xminus (XminConst f t) (XminConst f s)).

Definition StepApproxIntegrable {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (s t : CRcarrier (RealT (ElemFunc IS))) (ltst : 0 < s < t)
  : IntegrableFunction f
    -> IntegrableFunction (StepApprox f s t (snd ltst))
  := fun fInt => IntegrableScale _ _
  (IntegrableMinus (XminConst f t) (XminConst f s)
     (IntegrableMinConst f t fInt (CRlt_trans 0 s t (fst ltst) (snd ltst)))
     (IntegrableMinConst f s fInt (fst ltst))).

Lemma StepApproxBetween : forall {R : ConstructiveReals}
           (t : CRcarrier R) (tPos : 0 < t) (n : nat),
    0 < t*CR_of_Q _ (1-(1#Pos.of_nat (2*S n))) < t.
Proof.
  split.
  - apply CRmult_lt_0_compat. exact tPos. apply CR_of_Q_pos.
    unfold Qminus.
    rewrite <- (Qplus_opp_r (1 # Pos.of_nat (2 * S n))), Qplus_lt_l.
    unfold Qlt, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_lt_pos. rewrite Pos2Nat.inj_lt, Nat2Pos.id.
    simpl. apply le_n_S. rewrite Nat.add_comm. apply le_n_S, le_0_n.
    discriminate.
  - rewrite <- (CRmult_1_r t), CRmult_assoc. apply CRmult_lt_compat_l.
    exact tPos. rewrite CRmult_1_l, <- CR_of_Q_one. apply CR_of_Q_lt.
    apply (Qplus_lt_l _ _ ((1 # Pos.of_nat (2 * S n))-1)).
    ring_simplify. reflexivity.
Qed.

Lemma StepApproxCv : forall {R : ConstructiveReals} (t : CRcarrier R),
    CR_cv R (fun n => t*CR_of_Q _ (1-(1#Pos.of_nat (2*S n)))) t.
Proof.
  intros. apply (CR_cv_proper _ (1*t)). 2: apply CRmult_1_l.
  apply (CR_cv_eq _ (fun n : nat => CR_of_Q R (1 - (1 # Pos.of_nat (2 * S n))) * t)).
  intro n. apply CRmult_comm.
  apply CR_cv_scale. intro p. exists (Pos.to_nat p).
  intros.
  setoid_replace (CR_of_Q R (1 - (1 # Pos.of_nat (2 * S i))) - 1)
    with (-CR_of_Q R (1 # Pos.of_nat (2 * S i))).
  - rewrite CRabs_opp, CRabs_right. apply CR_of_Q_le.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. rewrite Pos2Nat.inj_le, Nat2Pos.id.
    2: discriminate. apply (le_trans _ _ _ H). simpl.
    apply le_S. apply (le_trans _ (i+0)).
    rewrite Nat.add_comm. apply le_refl.
    apply Nat.add_le_mono_l, le_0_n.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  - unfold Qminus. rewrite CR_of_Q_plus, CR_of_Q_opp, CR_of_Q_one.
    unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
    rewrite CRplus_0_l. reflexivity.
Qed.

Lemma StepApproxAbove :
  forall {R : ConstructiveReals} {X : Set}
    (f : PartialFunction X)
    (t : CRcarrier R) (tPos : 0 < t) (x : X)
    (xnD : nat -> Domain f x * Domain f x)
    (l : CRcarrier R),
    0 < l
    -> CR_cv R
             (fun n : nat =>
                partialApply
                  (StepApprox f (t * CR_of_Q R (1 - (1 # Pos.of_nat (2 * S n)))) t
                              (snd (StepApproxBetween t tPos n))) x (xnD n)) l
    -> t <= partialApply f x (fst (xnD O)).
Proof.
  intros. intro abs.
  destruct (CR_cv_open_below _ _ _ (StepApproxCv t) abs) as [n nmaj].
  assert (CR_cv R
         (fun n : nat =>
          partialApply
            (StepApprox f (t * CR_of_Q R (1 - (1 # Pos.of_nat (2 * S n)))) t
               (snd (StepApproxBetween t tPos n))) x (xnD n)) 0).
  intro p. exists n. intros. unfold StepApprox.
  rewrite applyXscale.
  setoid_replace (partialApply
       (Xminus (XminConst f t) (XminConst f (t * CR_of_Q R (1 - (1 # Pos.of_nat (2 * S i)))))) x
       (xnD i)) with (CRzero R).
  rewrite CRmult_0_r. unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
  rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRle_refl.
  destruct (xnD i).
  rewrite (applyXminus (XminConst f t)
                       (XminConst f (t * CR_of_Q R (1 - (1 # Pos.of_nat (2 * S i))))) x).
  rewrite applyXminConst, applyXminConst.
  rewrite CRmin_left, CRmin_left.
  unfold CRminus. rewrite (DomainProp f x d d0), CRplus_opp_r. reflexivity.
  specialize (nmaj i H1). rewrite (DomainProp f x d0 (fst (xnD 0%nat))).
  apply CRlt_asym, nmaj.
  specialize (nmaj i H1). rewrite (DomainProp f x d (fst (xnD 0%nat))).
  apply CRlt_asym, (CRlt_trans _ _ _ nmaj). apply StepApproxBetween, tPos.
  rewrite <- (CR_cv_unique _ _ _ H1 H0) in H. exact (CRlt_asym 0 0 H H).
Qed.

Lemma StepApproxBelow :
  forall {R : ConstructiveReals} {X : Set}
    (f : PartialFunction X)
    (t : CRcarrier R) (tPos : 0 < t) (x : X)
    (xnD : nat -> Domain f x * Domain f x)
    (l : CRcarrier R),
    l < 1
    -> CR_cv R
             (fun n : nat =>
                partialApply
                  (StepApprox f (t * CR_of_Q R (1 - (1 # Pos.of_nat (2 * S n)))) t
                              (snd (StepApproxBetween t tPos n))) x (xnD n)) l
    -> partialApply f x (fst (xnD O)) < t.
Proof.
  intros.
  destruct (CR_cv_open_above _ _ _ H0 H) as [k kmaj].
  specialize (kmaj k (le_refl k)).
  unfold StepApprox in kmaj. rewrite applyXscale in kmaj.
  apply (CRmult_lt_compat_l (t - t * CR_of_Q R (1 - (1 # Pos.of_nat (2 * S k)))))
    in kmaj.
  2: apply CRlt_minus, StepApproxBetween, tPos.
  rewrite <- CRmult_assoc, CRinv_r, CRmult_1_r, CRmult_1_l in kmaj.
  destruct (xnD k).
  rewrite (applyXminus
             (XminConst f t)
             (XminConst f (t * CR_of_Q R (1 - (1 # Pos.of_nat (2 * S k))))))
    in kmaj.
  assert (partialApply (XminConst f t) x d < t).
  { apply (CRplus_lt_reg_r
             (- partialApply (XminConst f (t * CR_of_Q R (1 - (1 # Pos.of_nat (2 * S k))))) x d0)).
    apply (CRlt_le_trans _ _ _ kmaj).
    apply CRplus_le_compat_l, CRopp_ge_le_contravar. apply CRmin_r. }
  rewrite applyXminConst in H1. rewrite CRmin_left in H1.
  rewrite (DomainProp f x _ d). exact H1.
  apply CRmin_lt_r in H1. rewrite <- H1. apply CRmin_r.
Qed.

Lemma AffineLe
  : forall {R : ConstructiveReals}
      (a b c d x low up : CRcarrier R),
    a * low + b <= c * low + d
    -> a * up + b <= c * up + d
    -> low <= x <= up
    -> a * x + b <= c * x + d.
Proof.
  intro R.
  assert (forall (a b x low up : CRcarrier R),
             0 <= a * low + b
             -> 0 <= a * up + b
             -> low <= x <= up
             -> 0 <= a * x + b).
  { intros.
    apply (CRle_trans _ (CRmin (a*low+b) (a*up+b))).
    apply CRmin_glb; assumption.
    rewrite CRplus_comm, (CRplus_comm (a*up)), <- CRmin_plus, CRplus_comm.
    apply CRplus_le_compat_r.
    intro abs. apply CRlt_min in abs. destruct abs.
    clear H H0.
    apply (CRplus_lt_compat_l R (-(a*x))) in c.
    rewrite CRplus_opp_l, CRopp_mult_distr_r, <- CRmult_plus_distr_l in c.
    pose proof (CRmult_pos_appart_zero _ _ c). destruct H.
    + rewrite <- (CRmult_0_r a) in c. apply CRmult_lt_reg_l in c.
      rewrite <- (CRplus_opp_l x) in c. apply CRplus_lt_reg_l in c.
      destruct H1. contradiction. exact c1.
    + apply CRopp_gt_lt_contravar in c0.
      do 2 rewrite CRopp_mult_distr_l in c0. apply CRmult_lt_reg_l in c0.
      destruct H1. contradiction. rewrite <- CRopp_0.
      apply CRopp_gt_lt_contravar, c1. }
  intros. apply (CRplus_le_reg_r (-(a*x+b))).
  rewrite CRplus_opp_r, CRopp_plus_distr, CRplus_assoc.
  rewrite (CRplus_comm d), <- CRplus_assoc, <- CRplus_assoc.
  rewrite CRopp_mult_distr_l, <- CRmult_plus_distr_r.
  rewrite CRplus_assoc. apply (H (c-a) (-b+d) x low up).
  3: exact H2.
  rewrite (CRplus_comm (-b)), <- CRplus_assoc.
  apply (CRplus_le_reg_r b).
  rewrite CRplus_0_l, CRplus_assoc, CRplus_opp_l, CRplus_0_r.
  unfold CRminus. rewrite CRmult_plus_distr_r, CRplus_comm, <- CRplus_assoc.
  apply (CRplus_le_reg_r (a*low)).
  rewrite CRplus_assoc, <- CRopp_mult_distr_l, CRplus_opp_l, CRplus_0_r.
  rewrite CRplus_comm, (CRplus_comm d). exact H0.
  rewrite (CRplus_comm (-b)), <- CRplus_assoc.
  apply (CRplus_le_reg_r b).
  rewrite CRplus_0_l, CRplus_assoc, CRplus_opp_l, CRplus_0_r.
  unfold CRminus. rewrite CRmult_plus_distr_r, CRplus_comm, <- CRplus_assoc.
  apply (CRplus_le_reg_r (a*up)).
  rewrite CRplus_assoc, <- CRopp_mult_distr_l, CRplus_opp_l, CRplus_0_r.
  rewrite CRplus_comm, (CRplus_comm d). exact H1.
Qed.

Lemma StepApproxLe
  : forall {R : ConstructiveReals}
      (c s1 t1 s2 t2 : CRcarrier R)
      (ltst1 : s1 < t1) (ltst2 : s2 < t2),
  s1 <= s2
  -> t1 <= t2
  -> CRinv R (t2 - s2) (inr (CRlt_minus s2 t2 ltst2)) *
    (CRmin c t2 + - CRmin c s2) <=
    CRinv R (t1 - s1) (inr (CRlt_minus s1 t1 ltst1)) *
    (CRmin c t1 + - CRmin c s1).
Proof.
  intros. destruct (CRltLinear R) as [_ s].
  destruct (s s2 c t2 ltst2).
  - rewrite (CRmin_right c s2), (CRmin_right c s1).
    2: apply (CRle_trans _ _ _ H), CRlt_asym, c0.
    2: apply CRlt_asym, c0.
    apply (CRmult_le_reg_l (t1-s1)). apply CRlt_minus, ltst1.
    rewrite <- CRmult_assoc, <- CRmult_assoc, CRinv_r, CRmult_1_l, CRmult_comm.
    apply (CRplus_le_reg_r s1). rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    apply CRmin_glb.
    + apply (CRplus_le_reg_r (-s1)).
      rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
      apply (CRmult_le_reg_r (t2-s2)). apply CRlt_minus, ltst2.
      rewrite CRmult_assoc, CRmult_assoc, CRinv_l, CRmult_1_r.
      rewrite CRplus_comm, CRmin_plus, CRmult_comm, <- CRmin_mult.
      2: apply CRlt_asym, CRlt_minus, ltst1.
      intro abs. apply CRlt_min in abs. destruct abs.
      rewrite (CRplus_comm (-s2)) in c2. apply CRmult_lt_reg_r in c2.
      2: apply CRlt_minus, ltst2. apply CRplus_lt_reg_r in c2.
      assert ((t1 - s1) * (- s2 + c) <= (c + - s1) * (t2 - s2)).
      { clear c1.
        rewrite CRplus_comm, CRmult_plus_distr_l.
        rewrite (CRmult_comm (c+-s1)), CRmult_plus_distr_l.
        apply (AffineLe _ _ _ _ _ s2 t1).
        do 2 rewrite <- CRmult_plus_distr_l.
        rewrite CRplus_opp_r, CRmult_0_r.
        apply CRmult_le_0_compat. apply CRlt_asym, CRlt_minus, ltst2.
        rewrite <- (CRplus_opp_r s1). apply CRplus_le_compat_r, H.
        do 2 rewrite <- CRmult_plus_distr_l.
        rewrite CRmult_comm. apply CRmult_le_compat_r.
        apply CRlt_asym, CRlt_minus, ltst1.
        apply CRplus_le_compat_r, H0.
        split; apply CRlt_asym; assumption. }
      contradiction.
    + apply (CRplus_le_reg_r (-s1)). rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
      apply (CRmult_le_reg_r (t2-s2)). apply CRlt_minus, ltst2.
      rewrite CRmult_assoc, CRmult_assoc, CRinv_l, CRmult_1_r.
      rewrite CRmult_comm. apply CRmult_le_compat_l.
      apply CRlt_asym, CRlt_minus, ltst1.
      apply CRplus_le_compat_r, CRmin_r.
  - rewrite CRmin_left. 2: apply CRlt_asym, c0.
    destruct (s s1 c t1 ltst1).
    + rewrite (CRmin_right c s1). 2: apply CRlt_asym, c1.
      apply (CRmult_le_reg_l (t1-s1)). apply CRlt_minus, ltst1.
      rewrite <- CRmult_assoc, <- CRmult_assoc, CRinv_r, CRmult_1_l.
      apply (CRplus_le_reg_r s1). rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply CRmin_glb.
      apply (CRplus_le_reg_r (-s1)). rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
      rewrite CRmult_comm.
      apply (CRmult_le_reg_r (t2-s2)). apply CRlt_minus, ltst2.
      rewrite CRmult_assoc, CRmult_assoc, CRinv_l, CRmult_1_r.
      setoid_replace (- CRmin c s2) with (-(1) * CRmin c s2).
      rewrite <- CRmax_min_mult_neg. do 2 rewrite <- CRopp_mult_distr_l, CRmult_1_l.
      rewrite CRmax_plus, CRmult_comm, <- CRmax_mult. apply CRmax_lub.
      rewrite CRplus_opp_r, CRmult_0_r. rewrite <- (CRmult_0_r (c-s1)).
      apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, c1.
      apply CRlt_asym, CRlt_minus, ltst2.
      rewrite CRmult_plus_distr_l, (CRmult_comm (c+-s1)), CRmult_plus_distr_l.
      apply (AffineLe _ _ _ _ _ s1 t2).
      do 2 rewrite <- CRmult_plus_distr_l. rewrite CRplus_opp_r, CRmult_0_r.
      rewrite <- (CRmult_0_r (t1-s1)). apply CRmult_le_compat_l.
      apply CRlt_asym, CRlt_minus, ltst1.
      rewrite <- (CRplus_opp_r s2). apply CRplus_le_compat_r, H.
      do 2 rewrite <- CRmult_plus_distr_l. rewrite CRmult_comm.
      apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltst2.
      apply CRplus_le_compat_r, H0.
      split; apply CRlt_asym; assumption.
      apply CRlt_asym, CRlt_minus, ltst1.
      apply (CRplus_le_reg_l 1). rewrite CRplus_opp_r, CRplus_0_r.
      apply CRlt_asym, CRzero_lt_one.
      rewrite <- CRopp_mult_distr_l, CRmult_1_l. reflexivity.
      apply (CRplus_le_reg_r (-s1)). rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
      rewrite <- (CRmult_1_r (t1 + - s1)), CRmult_assoc.
      apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltst1.
      apply (CRmult_le_reg_l (t2-s2)). apply CRlt_minus, ltst2.
      rewrite <- CRmult_assoc, CRinv_r, CRmult_1_l, CRmult_1_r.
      apply (CRplus_le_reg_r (CRmin c s2)).
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      rewrite CRmin_plus. apply CRmin_glb.
      apply (CRplus_le_reg_l s2). rewrite <- CRplus_assoc. apply CRplus_le_compat_r.
      rewrite CRplus_comm. unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply CRlt_asym, ltst2. unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply CRlt_asym, c0.
    + clear c0. rewrite (CRmin_left c t1). 2: apply CRlt_asym, c1.
      apply (CRmult_le_reg_l (t2-s2)). apply CRlt_minus, ltst2.
      rewrite <- CRmult_assoc, CRinv_r, CRmult_1_l.
      apply (CRplus_le_reg_l (-c)).
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      setoid_replace (- CRmin c s2) with (-(1) * CRmin c s2).
      2: rewrite <- CRopp_mult_distr_l, CRmult_1_l; reflexivity.
      rewrite <- CRmax_min_mult_neg. apply CRmax_lub.
      rewrite <- CRopp_mult_distr_l, CRmult_1_l.
      apply (CRle_trans _ (-c +0)). rewrite CRplus_0_r; apply CRle_refl.
      apply CRplus_le_compat_l. apply (CRle_trans _ ((t2-s2)*0)).
      rewrite CRmult_0_r; apply CRle_refl. apply CRmult_le_compat_l.
      apply CRlt_asym, CRlt_minus, ltst2.
      apply (CRmult_le_reg_l (t1-s1)). apply CRlt_minus, ltst1.
      rewrite CRmult_0_r, <- CRmult_assoc, CRinv_r, CRmult_1_l.
      rewrite <- (CRplus_opp_r (CRmin c s1)). apply CRplus_le_compat_r, CRmin_l.
      rewrite <- CRopp_mult_distr_l, CRmult_1_l.
      apply (CRplus_le_reg_l c).
      rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l, CRmult_comm.
      apply (CRmult_le_reg_l (t1-s1)). apply CRlt_minus, ltst1.
      rewrite <- CRmult_assoc, <- CRmult_assoc, CRinv_r, CRmult_1_l.
      rewrite CRmult_plus_distr_r.
      apply (CRplus_le_reg_l (-(c*(t2-s2)))).
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite (CRmult_comm (-CRmin c s1)), <- CRopp_mult_distr_r.
      rewrite <- CRmin_mult. 2: apply CRlt_asym, CRlt_minus, ltst2.
      rewrite <- CRopp_involutive, CRopp_plus_distr, CRopp_involutive.
      apply CRopp_ge_le_contravar.
      intro abs. apply CRlt_min in abs. destruct abs.
      rewrite <- (CRplus_0_r ((t2-s2)*c)), (CRmult_comm (t2-s2)) in c0.
      apply CRplus_lt_reg_l in c0.
      apply (CRplus_lt_compat_l R ((t1 - s1) * (c + - s2))) in c0.
      rewrite CRplus_opp_r, CRplus_0_r in c0.
      rewrite <- (CRmult_0_r (t1-s1)) in c0. apply CRmult_lt_reg_l in c0.
      2: apply CRlt_minus, ltst1. rewrite <- (CRplus_opp_r s2) in c0.
      apply CRplus_lt_reg_r in c0.
      assert ((t2-s2)*s1 <= c * (t2 - s2) + - ((t1 - s1) * (c + - s2))).
      { apply (CRplus_le_reg_r ((t1 - s1) * (c + - s2))).
        rewrite CRplus_assoc, CRplus_opp_l, CRplus_comm.
        rewrite CRmult_plus_distr_l, CRplus_assoc, (CRmult_comm c).
        apply (AffineLe _ _ _ _ _ s2 t1).
        3: split; apply CRlt_asym; assumption.
        rewrite CRplus_0_r, <- CRplus_assoc, <- CRopp_mult_distr_r.
        rewrite CRplus_opp_r, CRplus_0_l. apply CRmult_le_compat_l.
        apply CRlt_asym, CRlt_minus, ltst2. exact H.
        rewrite CRplus_0_r, <- CRplus_assoc, <- CRmult_plus_distr_l.
        apply (CRplus_le_reg_r (-((t2-s2)*s1))).
        rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r, CRopp_mult_distr_r.
        rewrite <- CRmult_plus_distr_l, CRmult_comm.
        apply CRmult_le_compat_r. apply CRlt_asym, CRlt_minus, ltst1.
        apply CRplus_le_compat_r, H0. }
      contradiction. apply (CRplus_le_reg_l 1).
      rewrite CRplus_opp_r, CRplus_0_r. apply CRlt_asym, CRzero_lt_one.
Qed.

Definition InverseImageIntegrableGivenLimit
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fInt : IntegrableFunction f)
           (t : CRcarrier (RealT (ElemFunc IS))) (tPos : 0 < t)
  : CR_cauchy _ (fun n:nat => Integral (StepApproxIntegrable
                                      f _ t (StepApproxBetween t tPos n) fInt))
    -> { limInt : IntegrableSet (fun x => exists xD:Domain f x, t <= partialApply f x xD)
       & CR_cv _ (fun n:nat => Integral (StepApproxIntegrable
                                      f _ t (StepApproxBetween t tPos n) fInt))
               (MeasureSet limInt) }.
Proof.
  intro cv. apply CR_complete in cv. destruct cv as [a cv].
  destruct (IntegralMonotoneConvergenceDecr
              IS _ (fun n => StepApproxIntegrable
                            f _ _ (StepApproxBetween t tPos n) fInt) a)
    as [limInt c].
  - intros n x xdf xdg. destruct xdf, xdg. unfold StepApprox.
    rewrite applyXscale, applyXscale.
    rewrite (applyXminus
               (XminConst f t)
               (XminConst f (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S (S n))))))).
    rewrite (applyXminus
               (XminConst f t)
               (XminConst f (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S n)))))).
    do 4 rewrite applyXminConst.
    rewrite (DomainProp f x d2 d), (DomainProp f x d1 d), (DomainProp f x d0 d).
    apply StepApproxLe. 2: apply CRle_refl.
    apply CRmult_le_compat_l. apply CRlt_asym, tPos.
    apply CR_of_Q_le. apply Qplus_le_r, Qopp_le_compat.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. rewrite Pos2Nat.inj_le, Nat2Pos.id, Nat2Pos.id.
    2: discriminate. 2: discriminate.
    simpl. apply le_n_S, le_S. apply Nat.add_le_mono_l.
    apply le_S, le_refl.
  - exact cv.
  - assert (PartialRestriction
              (XpointwiseLimit
           (fun n : nat =>
            StepApprox f (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S n)))) t
                       (snd (StepApproxBetween t tPos n))))
              (CharacFunc (fun x => exists xD:Domain f x, t <= partialApply f x xD))) as res.
    { clear c limInt cv a. split.
      + intros x [xnD xnlim]. simpl in xnD.
        apply CR_complete in xnlim. destruct xnlim as [l xnlim].
        destruct (CRltLinear (RealT (ElemFunc IS))).
        destruct (s 0 l 1 (CRzero_lt_one _)).
        left. exists (fst (xnD O)).
        exact (StepApproxAbove f t tPos x xnD l c xnlim).
        right. intros [xD abs]. apply abs. clear abs.
        rewrite (DomainProp f x xD (fst (xnD O))).
        exact (StepApproxBelow f t tPos x xnD l c xnlim).
      + intros. apply applyPointwiseLimit. destruct xG.
        apply (CR_cv_eq _ (fun _ => 1)). 2: apply CR_cv_const.
        intro n. destruct xD as [xnD H].
        unfold StepApprox. rewrite applyXscale.
        setoid_replace (partialApply
                          (Xminus (XminConst f t)
       (XminConst f (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S n)))))) x
                          (xnD n))
          with (t - t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S n)))).
        rewrite CRinv_l. reflexivity. destruct (xnD n).
        apply CRplus_morph. rewrite applyXminConst.
        rewrite CRmin_right. reflexivity.
        destruct e. rewrite (DomainProp f x d x0). exact H0.
        rewrite applyXscale. rewrite applyXminConst, CRmin_right.
        rewrite <- CRopp_mult_distr_l, CRmult_1_l. reflexivity.
        destruct e. rewrite (DomainProp f x d0 x0).
        apply (CRle_trans _ t). 2: exact H0.
        apply CRlt_asym, StepApproxBetween, tPos.
        destruct xD as [xnD H]. simpl in xnD.
        apply CR_complete in H. destruct H as [l lcv].
        destruct (CRltLinear (RealT (ElemFunc IS))).
        destruct (s 0 l 1 (CRzero_lt_one _)).
        exfalso. apply n. exists (fst (xnD O)).
        exact (StepApproxAbove f t tPos x xnD l c lcv).
        pose proof (StepApproxBelow f t tPos x xnD l c lcv).
        destruct (CR_cv_open_below _ _ _ (StepApproxCv t) H) as [k kmaj].
        intro i. exists k. intros.
        setoid_replace (partialApply
       (StepApprox f
          (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S i0)))) t
          (snd (StepApproxBetween t tPos i0))) x (xnD i0))
          with (CRzero (RealT (ElemFunc IS))).
        simpl. unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
        rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
        apply CRle_refl. unfold StepApprox. rewrite applyXscale.
        setoid_replace (partialApply
    (Xminus (XminConst f t)
       (XminConst f
          (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S i0)))))) x
    (xnD i0) ) with (CRzero (RealT (ElemFunc IS))).
        rewrite CRmult_0_r. reflexivity. destruct (xnD i0).
        rewrite (applyXminus (XminConst f t)
                             (XminConst f (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S i0))))) ).
        rewrite applyXminConst, applyXminConst, CRmin_left, CRmin_left.
        unfold CRminus; rewrite (DomainProp f x d0 d), CRplus_opp_r; reflexivity.
        rewrite (DomainProp f x d0 (fst (xnD O))).
        apply CRlt_asym, kmaj, H0.
        rewrite (DomainProp f x d (fst (xnD O))).
        apply CRlt_asym, H. }
    exists (IntegrableFunctionExtensional _ _ res limInt).
    unfold MeasureSet. rewrite IntegralRestrict.
    exact (CR_cv_proper _ _ _ cv (CReq_sym _ _ c)).
Qed.

(*
  To prove that the inverse image {t <= f} is integrable, we have reduced
  the problem of giving a sequence of representative L-functions to the
  problem of the convergence of a non-increasing and bounded sequence :
  lim_{s -> t} Integral (StepApproxIntegrable f s t).

  Classically this convergence is automatic at each t, which gives a
  non-increasing function of t that is caglad. It is well-known classically
  that those functions are almost everywhere continuous,
  with at most a countable infinity of jump points.

  Constructively this convergence is not automatic, so we are left with
  studying the function of 2 variables
  fun s t => Integral (StepApproxIntegrable f s t) with 0 < s < t.
  We will define constructively what t's are jump points of the intended
  limit function, prove that they are at most countable, and prove that
  outside of them the limit exists constructively. Besides at those
  continuity points t we will also have equal measures for the subsets
  {t <= f} and {t < f}.
*)


(* The monotone property extended constructively in 2 variables. *)
Lemma StepApproxIntegralIncr
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (s1 t1 s2 t2 : CRcarrier (RealT (ElemFunc IS)))
      (ltst1 : 0 < s1 < t1) (ltst2 : 0 < s2 < t2),
    s1 <= s2
    -> t1 <= t2
    -> Integral (StepApproxIntegrable f s2 t2 ltst2 fInt)
      <= Integral (StepApproxIntegrable f s1 t1 ltst1 fInt).
Proof.
  intros. apply IntegralNonDecreasing.
  intros x xdf xdg. simpl. destruct xdf, xdg.
  rewrite (DomainProp f x d2 d), (DomainProp f x d1 d), (DomainProp f x d0 d).
  generalize (partialApply f x d). intro c.
  rewrite <- CRopp_mult_distr_l, CRmult_1_l.
  rewrite <- CRopp_mult_distr_l, CRmult_1_l.
  apply StepApproxLe; assumption.
Qed.

Record IntervalExtension {R : ConstructiveReals} {x y : CRcarrier R} : Set
  := {
      ext_eta : CRcarrier R;
      left_ordered : 0 < x - ext_eta < x;
      right_ordered : y < y + ext_eta;
    }.

Lemma IntExtRightPos : forall {R : ConstructiveReals} {x y : CRcarrier R}
                         (IntExt : @IntervalExtension R x y),
    x <= y -> 0 < y.
Proof.
  intros. apply (CRlt_le_trans _ x).
  apply (CRlt_trans _ _ _ (fst (left_ordered IntExt)) (snd (left_ordered IntExt))).
  exact H.
Qed.

(* Now for t1 <= t2 we bound the difference of measures of
   { t1 <= f } and { t2 <= f }, left limit at t1 and right
   limit at t2, ie including both jumps at the extreme points t1 and t2. *)
Definition StepApproxBound
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fInt : IntegrableFunction f)
           (t1 t2 b : CRcarrier (RealT (ElemFunc IS)))
           (let1t2 : t1 <= t2)
  : Set
  := { ext : @IntervalExtension _ t1 t2
     & Integral (StepApproxIntegrable
                   f (t1 - ext_eta ext) t1
                   (left_ordered ext) fInt)
       - Integral (StepApproxIntegrable
                     f t2 (t2 + ext_eta ext)
                     (pair (IntExtRightPos ext let1t2)
                           (right_ordered ext)) fInt)
       < b }.

(* Exlude jumps at extreme points t1, t2 for open intervals ]t1,t2[. *)
Definition StepApproxBoundOpen
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fInt : IntegrableFunction f)
           (t1 t2 b : CRcarrier (RealT (ElemFunc IS)))
  : Prop
  := forall x y u v (ltxy : 0 < x < y) (ltuv : 0 < u < v),
    t1 < x
    -> y <= u
    -> v < t2
    -> Integral (StepApproxIntegrable f x y ltxy fInt)
      - Integral (StepApproxIntegrable f u v ltuv fInt)
      <= b.

Lemma StepApproxBoundPos
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (t1 t2 b : CRcarrier (RealT (ElemFunc IS))) (let1t2 : t1 <= t2),
    StepApproxBound f fInt t1 t2 b let1t2 -> 0 < b.
Proof.
  intros. destruct H.
  apply (CRle_lt_trans _ (Integral (StepApproxIntegrable f (t1 - ext_eta x) t1 (left_ordered x) fInt) -
      Integral
        (StepApproxIntegrable f t2 (t2 + ext_eta x) (IntExtRightPos x let1t2, right_ordered x) fInt))).
  2: exact c.
  apply (CRplus_le_reg_r (Integral (StepApproxIntegrable f t2 (t2 + ext_eta x) (IntExtRightPos x let1t2, right_ordered x) fInt))).
  unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_0_l.
  clear c. apply StepApproxIntegralIncr. destruct x. simpl.
  apply (CRle_trans _ t1). apply CRlt_asym, left_ordered0.
  exact let1t2. destruct x. simpl.
  apply (CRle_trans _ t2). exact let1t2.
  apply CRlt_asym, right_ordered0.
Qed.

(* It is easier to detect that a monotone sequence converges. *)
Lemma StepApproxBoundCv
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (t : CRcarrier (RealT (ElemFunc IS))) (tPos : 0 < t),
    (forall b : CRcarrier (RealT (ElemFunc IS)),
        0 < b -> StepApproxBound f fInt t t b (CRle_refl t))
    -> CR_cauchy _ (fun n:nat => Integral (StepApproxIntegrable
                                      f _ t (StepApproxBetween t tPos n) fInt)).
Proof.
  intros. intro p.
  destruct (H (CR_of_Q _ (1 # p))) as [ext extmaj].
  apply CR_of_Q_pos. reflexivity.
  assert (0 < ext_eta ext).
  { destruct ext; clear extmaj. simpl.
    apply (CRplus_lt_reg_l _ t). rewrite CRplus_0_r. exact right_ordered0. }
  destruct (CR_cv_open_below _ (t-ext_eta ext) t (StepApproxCv t)) as [n nmaj].
  apply ext. exists n. intros. destruct (le_lt_dec i j).
  - rewrite CRabs_right.
    apply (CRle_trans _ (Integral (StepApproxIntegrable f (t - ext_eta ext) t (left_ordered ext) fInt) -
           Integral
             (StepApproxIntegrable f t (t + ext_eta ext)
                                   (IntExtRightPos ext (CRle_refl t), right_ordered ext) fInt))).
    2: apply CRlt_asym; exact extmaj. apply CRplus_le_compat.
    apply StepApproxIntegralIncr. apply CRlt_asym, nmaj, H1.
    apply CRle_refl. apply CRopp_ge_le_contravar.
    apply StepApproxIntegralIncr. apply CRlt_asym, StepApproxBetween, tPos.
    apply CRlt_asym, ext.
    apply (CRplus_le_reg_r (Integral
    (StepApproxIntegrable f (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S j)))) t
                          (StepApproxBetween t tPos j) fInt))).
    unfold CRminus. rewrite CRplus_0_l, CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    apply StepApproxIntegralIncr. 2: apply CRle_refl.
    apply CRmult_le_compat_l. apply CRlt_asym, tPos.
    apply CR_of_Q_le, Qplus_le_r, Qopp_le_compat.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. rewrite Pos2Nat.inj_le, Nat2Pos.id, Nat2Pos.id.
    apply Nat.mul_le_mono_nonneg_l. auto. apply le_n_S, l.
    discriminate. discriminate.
  - rewrite CRabs_minus_sym. rewrite CRabs_right.
    apply (CRle_trans _ (Integral (StepApproxIntegrable f (t - ext_eta ext) t (left_ordered ext) fInt) -
           Integral
             (StepApproxIntegrable f t (t + ext_eta ext)
                                   (IntExtRightPos ext (CRle_refl t), right_ordered ext) fInt))).
    2: apply CRlt_asym; exact extmaj. apply CRplus_le_compat.
    apply StepApproxIntegralIncr. apply CRlt_asym, nmaj, H2.
    apply CRle_refl. apply CRopp_ge_le_contravar.
    apply StepApproxIntegralIncr. apply CRlt_asym, StepApproxBetween, tPos.
    apply CRlt_asym, ext.
    apply (CRplus_le_reg_r (Integral
    (StepApproxIntegrable f (t * CR_of_Q (RealT (ElemFunc IS)) (1 - (1 # Pos.of_nat (2 * S i)))) t
                          (StepApproxBetween t tPos i) fInt))).
    unfold CRminus. rewrite CRplus_0_l, CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    apply StepApproxIntegralIncr. 2: apply CRle_refl.
    apply CRmult_le_compat_l. apply CRlt_asym, tPos.
    apply CR_of_Q_le, Qplus_le_r, Qopp_le_compat.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. rewrite Pos2Nat.inj_le, Nat2Pos.id, Nat2Pos.id.
    apply Nat.mul_le_mono_nonneg_l. auto. apply le_S, l.
    discriminate. discriminate.
Qed.

Definition BinarySubdiv {R : ConstructiveReals} (a b : CRcarrier R) (n i : nat)
  : CRcarrier R
  := a + CR_of_Q R (Z.of_nat i # 1) * (b-a) * CRpow (CR_of_Q R ((/2))) n.

Lemma BinarySubdivIncr
  : forall {R : ConstructiveReals} (a b : CRcarrier R) (n i : nat),
    0 < a < b
    -> 0 < BinarySubdiv a b n i < BinarySubdiv a b n (S i).
Proof.
  intros. assert (0 < (b - a) * CRpow (CR_of_Q R (/ 2)) n).
  { apply CRmult_lt_0_compat.
    rewrite <- (CRplus_opp_r a). apply CRplus_lt_compat_r, H.
    apply pow_lt. apply CR_of_Q_pos. reflexivity. }
  split.
  - unfold BinarySubdiv. apply (CRlt_le_trans _ (a + 0)).
    rewrite CRplus_0_r. exact (fst H).
    apply CRplus_le_compat_l. rewrite CRmult_assoc.
    apply CRmult_le_0_compat.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. apply Zle_0_nat. apply CRlt_asym, H0.
  - apply CRplus_lt_compat_l.
    apply (CRplus_lt_reg_r (-(CR_of_Q R (Z.of_nat i # 1) * (b - a) * CRpow (CR_of_Q R (/ 2)) n))).
    rewrite CRplus_opp_r, CRmult_assoc, CRmult_assoc, CRopp_mult_distr_l.
    rewrite <- CRmult_plus_distr_r. apply CRmult_lt_0_compat. 2: exact H0.
    rewrite <- (CRplus_opp_r (CR_of_Q R (Z.of_nat i # 1))).
    apply CRplus_lt_compat_r. apply CR_of_Q_lt.
    unfold Qlt, Qnum, Qden. do 2 rewrite Z.mul_1_r. apply inj_lt, le_refl.
Qed.

Lemma BinarySubdivNext
  : forall {R : ConstructiveReals} (a b : CRcarrier R) (n i:nat),
    BinarySubdiv a b n i + CRpow (CR_of_Q R (1 # 2)) n * (b - a)
    == BinarySubdiv a b n (S i).
Proof.
  intros. unfold BinarySubdiv.
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite CRmult_assoc, <- (CRmult_comm (b-a)).
  rewrite <- (CRmult_1_l ((b - a) * CRpow (CR_of_Q R (1 # 2)) n)).
  rewrite (pow_proper (CR_of_Q R (/ 2)) (CR_of_Q R (1#2))).
  2: apply CR_of_Q_morph; reflexivity.
  rewrite <- CRmult_plus_distr_r.
  rewrite CRmult_assoc. apply CRmult_morph. 2: reflexivity.
  rewrite <- CR_of_Q_one, <- CR_of_Q_plus.
  apply CR_of_Q_morph. rewrite Qinv_plus_distr.
  unfold Qeq, Qnum, Qden. do 2 rewrite Z.mul_1_r.
  replace 1%Z with (Z.of_nat 1).
  rewrite <- Nat2Z.inj_add. rewrite Nat.add_comm. reflexivity. reflexivity.
Qed.

Lemma pow_nat : forall {R : ConstructiveReals} (a n : nat),
  CR_of_Q R (Z.of_nat (a ^ n) # 1) == CRpow (CR_of_Q R (Z.of_nat a # 1)) n.
Proof.
  induction n.
  - simpl. rewrite CR_of_Q_one. reflexivity.
  - simpl.
    setoid_replace (Z.of_nat (a * a ^ n) # 1)
      with ((Z.of_nat a # 1) * (Z.of_nat (a ^ n) # 1))%Q.
    rewrite CR_of_Q_mult. apply CRmult_morph. reflexivity.
    exact IHn. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

Lemma BinarySubdivInside
  : forall {R : ConstructiveReals} (a b : CRcarrier R) (n i : nat),
    a <= b
    -> le i (2 ^ n)
    -> a <= BinarySubdiv a b n i <= b.
Proof.
  split.
  - apply (CRle_trans _ (a+0)). rewrite CRplus_0_r. apply CRle_refl.
    apply CRplus_le_compat_l. apply CRmult_le_0_compat.
    apply CRmult_le_0_compat. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. destruct i; discriminate.
    rewrite <- (CRplus_opp_r a). apply CRplus_le_compat_r, H.
    apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  - unfold BinarySubdiv. apply (CRplus_le_reg_l (-a)).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    rewrite (CRplus_comm (-a)), <- (CRmult_comm (b-a)), <- (CRmult_1_r (b+-a)).
    rewrite CRmult_assoc. apply CRmult_le_compat_l.
    rewrite <- (CRplus_opp_r a). apply CRplus_le_compat_r, H.
    apply (CRmult_le_reg_r (CRpow (CR_of_Q R 2) n)).
    apply pow_lt, CR_of_Q_pos. reflexivity.
    rewrite CRmult_assoc, pow_mult.
    rewrite (pow_proper (CR_of_Q R (/ 2) * CR_of_Q R 2) 1).
    rewrite pow_one, CRmult_1_r, CRmult_1_l.
    apply (CRle_trans _ (CR_of_Q R (Z.of_nat (2^n)#1))).
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    rewrite Z.mul_1_r, Z.mul_1_r. apply Nat2Z.inj_le, H0.
    rewrite <- (pow_nat 2). apply CRle_refl.
    rewrite <- CR_of_Q_mult, <- CR_of_Q_one. apply CR_of_Q_morph. reflexivity.
Qed.

Lemma BinarySubdivRight
  : forall {R : ConstructiveReals} (a b : CRcarrier R) (n : nat),
    a <= b
    -> BinarySubdiv a b n (2 ^ n) == b.
Proof.
  intros. unfold BinarySubdiv.
  apply (CRplus_eq_reg_l (-a)).
  rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, (CRplus_comm (-a)).
  rewrite <- (CRmult_comm (b-a)), <- (CRmult_1_r (b+-a)).
  rewrite CRmult_assoc. apply CRmult_morph. reflexivity.
  apply (CRmult_eq_reg_r (CRpow (CR_of_Q R 2) n)).
  left. apply pow_lt, CR_of_Q_pos. reflexivity.
  rewrite CRmult_assoc, CRmult_1_l, pow_mult.
  rewrite (pow_proper (CR_of_Q R (/ 2) * CR_of_Q R 2) 1).
  rewrite pow_one, CRmult_1_r.
  apply (pow_nat 2).
  rewrite <- CR_of_Q_mult, <- CR_of_Q_one. apply CR_of_Q_morph. reflexivity.
Qed.

Fixpoint FindCrossingPoint {R : ConstructiveReals}
         (un : nat -> CRcarrier R) (N : nat) (alpha : CRcarrier R) { struct N }
  : (forall n:nat, un (S n) <= un n)
    -> (forall n:nat, CRapart R alpha (un n))
    -> alpha < un O
    -> { k : nat  &  (le k N)
                  * (sum (k = N) (un (S k) < alpha))
                  * (alpha < un k) }%type. (* besides k is unique *)
Proof.
  intros. destruct N.
  - exists O. split. split. exact (le_refl O). left. reflexivity. exact H1.
  - destruct (H0 (S N)).
    + exists (S N). split. split. exact (le_refl (S N)).
      left. reflexivity. exact c.
    + destruct (FindCrossingPoint R un N alpha H H0 H1) as [k kmaj].
      exists k. split. split. apply le_S, (fst kmaj). right.
      destruct kmaj, p, s. subst k. exact c. exact c1. exact (snd kmaj).
Qed.

(* Search the jump points in the binary discretization of interval [a,b].
   Allows to build incrementally better approximations of them.
   Also, being countable, we can use a jump size epsilon that is
   appart of them all. *)
Definition StepApproxDiscretize
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fInt : IntegrableFunction f)
           (a b eta : CRcarrier (RealT (ElemFunc IS)))
           (aPos : 0 < a) (ltab : a < b)
           (aeta : 0 < a - eta < a) (beta : 0 < b < b + eta)
           (n i : nat) (* Cut [a,b] into 2^n pieces *)
  : CRcarrier (RealT (ElemFunc IS))
  := match i with
     | O => Integral (StepApproxIntegrable f (a - eta) a aeta fInt)
     | S j => if le_lt_dec (S (2 ^ n)) i
             then Integral (StepApproxIntegrable f b (b + eta) beta fInt)
             else Integral (StepApproxIntegrable
                         f (BinarySubdiv a b n j)
                         (BinarySubdiv a b n (S j))
                         (BinarySubdivIncr a b n j (pair aPos ltab)) fInt)
     end.

Lemma StepApproxDiscretizeDecr
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a b eta : CRcarrier (RealT (ElemFunc IS)))
      (aPos : 0 < a) (ltab : a < b)
      (aeta : 0 < a - eta < a) (beta : 0 < b < b + eta)
      (n i j : nat),
    le i j
    -> StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n j
      <= StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n i.
Proof.
  induction j.
  - intros. inversion H. apply CRle_refl.
  - intros. apply Nat.le_succ_r in H. destruct H.
    2: subst i; apply CRle_refl.
    apply (CRle_trans _ (StepApproxDiscretize
                           f fInt a b eta aPos ltab aeta beta n j)).
    2: exact (IHj H). destruct j.
    + unfold StepApproxDiscretize.
      destruct (le_lt_dec (S (2 ^ n)) 1). exfalso.
      apply le_S_n in l. inversion l.
      pose proof (Nat.pow_gt_lin_r 2 n (le_refl _)). rewrite H1 in H0.
      inversion H0. apply StepApproxIntegralIncr.
      apply (CRle_trans _ a). apply CRlt_asym, (snd aeta).
      apply BinarySubdivInside. apply CRlt_asym, ltab. apply le_0_n.
      apply BinarySubdivInside. apply CRlt_asym, ltab. apply le_S_n, l.
    + unfold StepApproxDiscretize.
      destruct (le_lt_dec (S (2 ^ n)) (S (S j))), (le_lt_dec (S (2 ^ n)) (S j)).
      apply CRle_refl.
      apply StepApproxIntegralIncr.
      apply BinarySubdivInside. apply CRlt_asym, ltab.
      apply le_S_n in l0. apply (le_trans _ (S j)).
      apply le_S, le_refl. exact l0.
      apply (CRle_trans _ b). apply BinarySubdivInside.
      apply CRlt_asym, ltab. apply le_S_n, l0. apply CRlt_asym, (snd beta).
      exfalso. pose proof (lt_le_trans _ _ _ l l0).
      apply (lt_not_le _ _ H0). apply le_S, le_refl.
      apply StepApproxIntegralIncr.
      apply CRlt_asym, BinarySubdivIncr. exact (pair aPos ltab).
      apply CRlt_asym, BinarySubdivIncr. exact (pair aPos ltab).
Qed.

Lemma StepApproxDiscretizeRefineDecr
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a b eta : CRcarrier (RealT (ElemFunc IS)))
      (aPos : 0 < a) (ltab : a < b)
      (aeta : 0 < a - eta < a) (beta : 0 < b < b + eta)
      (n i j : nat),
    le (2*j) i
    -> StepApproxDiscretize
        f fInt a b eta aPos ltab aeta beta (S n) i
      <= StepApproxDiscretize
          f fInt a b eta aPos ltab aeta beta n j.
          (* Integral between a + (b-a)*(j-1)/2^n and a + (b-a)*j/2^n *)
Proof.
  intros. unfold StepApproxDiscretize. destruct j,i.
  - apply CRle_refl.
  - clear H. destruct (le_lt_dec (S (2 ^ S n)) (S i)).
    apply StepApproxIntegralIncr.
    apply (CRle_trans _ a). apply CRlt_asym, (snd aeta). apply CRlt_asym, ltab.
    apply (CRle_trans _ b). apply CRlt_asym, ltab. apply CRlt_asym, (snd beta).
    apply StepApproxIntegralIncr.
    apply (CRle_trans _ a). apply CRlt_asym, (snd aeta).
    apply BinarySubdivInside. apply CRlt_asym, ltab.
    apply le_S_n in l. apply (le_trans _ (S i)). apply le_S, le_refl.
    exact l. apply BinarySubdivInside. apply CRlt_asym, ltab.
    apply le_S_n, l.
  - exfalso. inversion H.
  - destruct (le_lt_dec (S (2 ^ n)) (S j)), (le_lt_dec (S (2 ^ S n)) (S i)).
    + apply CRle_refl.
    + exfalso. apply le_S_n in l0.
      apply (le_trans _ _ _ H) in l0. clear H.
      apply (Nat.mul_le_mono_pos_l _ _ 2) in l0.
      apply (le_trans _ _ _ l) in l0. apply (le_not_lt _ _ l0 (le_refl _)).
      apply le_n_S, le_0_n.
    + apply StepApproxIntegralIncr.
      apply BinarySubdivInside. apply CRlt_asym, ltab.
      apply le_S_n in l. apply (le_trans _ (S j)).
      apply le_S, le_refl. exact l. apply (CRle_trans _ b).
      apply BinarySubdivInside. apply CRlt_asym, ltab.
      apply le_S_n, l. apply CRlt_asym, (snd beta).
    + apply StepApproxIntegralIncr.
      apply CRplus_le_compat_l.
      do 2 rewrite <- (CRmult_comm (b-a)), CRmult_assoc.
      apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltab.
      simpl (CRpow (CR_of_Q (RealT (ElemFunc IS)) (/ 2)) (S n)).
      rewrite <- CRmult_assoc. apply CRmult_le_compat_r.
      apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_mult. apply CR_of_Q_le.
      apply Qle_shift_div_l. reflexivity.
      unfold Qmult, Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
      replace 2%Z with (Z.of_nat 2). 2: reflexivity.
      rewrite <- Nat2Z.inj_mul. apply Nat2Z.inj_le.
      apply le_S_n. apply (le_trans _ (2*S j)). 2: exact H.
      rewrite Nat.mul_comm.
      simpl. rewrite Nat.add_0_r, Nat.add_succ_r. apply le_S, le_refl.
      apply CRplus_le_compat_l.
      do 2 rewrite <- (CRmult_comm (b-a)), CRmult_assoc.
      apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltab.
      simpl (CRpow (CR_of_Q (RealT (ElemFunc IS)) (/ 2)) (S n)).
      rewrite <- CRmult_assoc. apply CRmult_le_compat_r.
      apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_mult. apply CR_of_Q_le.
      apply Qle_shift_div_l. reflexivity.
      unfold Qmult, Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
      replace 2%Z with (Z.of_nat 2). 2: reflexivity.
      rewrite <- Nat2Z.inj_mul. apply Nat2Z.inj_le.
      apply (le_trans _ (2*S j)). 2: exact H.
      rewrite Nat.mul_comm. apply le_refl.
Qed.

Lemma StepApproxDiscretizeRefineIncr
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a b eta : CRcarrier (RealT (ElemFunc IS)))
      (aPos : 0 < a) (ltab : a < b)
      (aeta : 0 < a - eta < a) (beta : 0 < b < b + eta)
      (n i j : nat),
    le (S i) (2*j)
    -> StepApproxDiscretize
        f fInt a b eta aPos ltab aeta beta n j
      (* Integral between a + (b-a)*(j-1)/2^n and a + (b-a)*j/2^n *)
      <= StepApproxDiscretize
          f fInt a b eta aPos ltab aeta beta (S n) i.
Proof.
  intros. unfold StepApproxDiscretize.
  destruct j. exfalso; inversion H. destruct i.
  - destruct (le_lt_dec (S (2 ^ n)) (S j)).
    apply StepApproxIntegralIncr.
    apply (CRle_trans _ a). apply CRlt_asym, aeta. apply CRlt_asym, ltab.
    apply (CRle_trans _ b). apply CRlt_asym, ltab. apply CRlt_asym, beta.
    apply StepApproxIntegralIncr. apply (CRle_trans _ a).
    apply CRlt_asym, aeta.
    apply BinarySubdivInside. apply CRlt_asym, ltab.
    apply le_S_n in l. apply (le_trans _ (S j)). apply le_S, le_refl.
    exact l. apply BinarySubdivInside. apply CRlt_asym, ltab.
    apply le_S_n, l.
  - destruct (le_lt_dec (S (2 ^ n)) (S j)), (le_lt_dec (S (2 ^ S n)) (S i)).
    + apply CRle_refl.
    + apply StepApproxIntegralIncr.
      apply BinarySubdivInside. apply CRlt_asym, ltab.
      apply le_S_n in l0. apply (le_trans _ (S i)). apply le_S, le_refl.
      exact l0. apply (CRle_trans _ b).
      apply BinarySubdivInside. apply CRlt_asym, ltab.
      apply le_S_n, l0. apply CRlt_asym, (snd beta).
    + exfalso. apply le_S_n in l0. apply le_S_n in l.
      apply (le_trans _ _ (2^S n)) in H.
      apply (le_trans _ _ _ H) in l0. apply (le_not_lt _ _ l0).
      apply le_S, le_refl. apply Nat.mul_le_mono_nonneg_l.
      apply le_0_n. exact l.
    + clear l l0.
      replace (2 * S j)%nat with (S (S (2 * j))) in H.
      2: simpl; rewrite Nat.add_0_r, Nat.add_succ_r; reflexivity.
      apply le_S_n, le_S_n in H.
      apply StepApproxIntegralIncr.
      apply CRplus_le_compat_l.
      do 2 rewrite <- (CRmult_comm (b-a)), CRmult_assoc.
      apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltab.
      simpl (CRpow (CR_of_Q (RealT (ElemFunc IS)) (/ 2)) (S n)).
      rewrite <- CRmult_assoc. apply CRmult_le_compat_r.
      apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_mult. apply CR_of_Q_le.
      apply Qle_shift_div_r. reflexivity.
      unfold Qmult, Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
      replace 2%Z with (Z.of_nat 2). 2: reflexivity.
      rewrite <- (Nat2Z.inj_mul j 2). apply Nat2Z.inj_le.
      rewrite Nat.mul_comm. exact H.
      apply CRplus_le_compat_l.
      do 2 rewrite <- (CRmult_comm (b-a)), CRmult_assoc.
      apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltab.
      simpl (CRpow (CR_of_Q (RealT (ElemFunc IS)) (/ 2)) (S n)).
      rewrite <- CRmult_assoc. apply CRmult_le_compat_r.
      apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_mult. apply CR_of_Q_le.
      apply Qle_shift_div_r. reflexivity.
      unfold Qmult, Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
      replace 2%Z with (Z.of_nat 2). 2: reflexivity.
      rewrite <- (Nat2Z.inj_mul (S j) 2). apply Nat2Z.inj_le.
      replace (S j * 2)%nat with (S (S (2*j))). apply le_n_S.
      apply (le_trans _ _ _ H). apply le_S, le_refl.
      rewrite (Nat.mul_comm (S j)). simpl.
      rewrite Nat.add_0_r, Nat.add_succ_r. reflexivity.
Qed.

(* More points to approximate, so better approximation. *)
Lemma FindCrossingPointIncr
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a b eta alpha : CRcarrier (RealT (ElemFunc IS)))
      (aPos : 0 < a) (ltab : a < b)
      (aeta : 0 < a - eta < a) (beta : 0 < b < b + eta)
      (n i j : nat),
    ((i <= 2 ^ n)%nat *
     ((i = (2 ^ n)%nat) +
      (StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n (S i) < alpha)) *
     (alpha < StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n i))
    -> ((j <= 2 ^ S n)%nat *
       ((j = (2 ^ S n)%nat) +
        (StepApproxDiscretize
           f fInt a b eta aPos ltab aeta beta (S n) (S j) < alpha)) *
       (alpha < StepApproxDiscretize f fInt a b eta aPos ltab aeta beta (S n) j))
    -> BinarySubdiv a b n i
      <= BinarySubdiv a b (S n) j + (b-a) * CRpow (CR_of_Q _ (1#2)) (S n).
Proof.
  intros.
  destruct H,H0,p,p0. destruct s0.
  - subst j. rewrite BinarySubdivRight.
    apply (CRle_trans _ (b+0)). rewrite CRplus_0_r.
    apply BinarySubdivInside. apply CRlt_asym, ltab. exact l.
    apply CRplus_le_compat_l. apply CRmult_le_0_compat.
    apply CRlt_asym, CRlt_minus, ltab. apply pow_le.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    apply CRlt_asym, ltab.
  - destruct s. subst i. rewrite BinarySubdivRight. 2: apply CRlt_asym, ltab.
    destruct (le_lt_dec (2^S n) (S j)).
    + unfold BinarySubdiv.
      apply (CRplus_le_reg_l (-a)).
      rewrite <- CRplus_assoc, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite <- (CRmult_comm (b-a)), <- (CRmult_1_r (-a+b)).
      rewrite CRmult_assoc, <- CRmult_plus_distr_l, CRplus_comm.
      apply CRmult_le_compat_l.
      apply CRlt_asym, CRlt_minus, ltab.
      rewrite <- (CRmult_1_l (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) (S n))).
      rewrite <- CRmult_plus_distr_r.
      apply (CRmult_le_reg_r (CRpow (CR_of_Q _ (Z.of_nat 2 # 1)) (S n))).
      apply pow_lt. apply CR_of_Q_pos. reflexivity.
      rewrite CRmult_1_l, CRmult_assoc, pow_mult.
      rewrite (pow_proper (CR_of_Q (RealT (ElemFunc IS)) (/ 2) *
                           CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat 2 # 1)) 1).
      rewrite pow_one, <- pow_nat, CRmult_1_r.
      rewrite <- CR_of_Q_one, <- CR_of_Q_plus.
      apply CR_of_Q_le.
      unfold Qplus, Qle, Qnum, Qden. do 4 rewrite Z.mul_1_r.
      replace 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add.
      apply Nat2Z.inj_le. rewrite Nat.add_comm. exact l1.
      reflexivity.
      rewrite <- CR_of_Q_mult, <- CR_of_Q_one. apply CR_of_Q_morph.
      reflexivity.
    + exfalso. pose proof (CRlt_trans _ _ _ c1 c).
      apply (StepApproxDiscretizeRefineIncr
               f fInt a b eta aPos ltab aeta beta n (S j) (2^n)).
      2: exact H. unfold lt in l1.
      replace (2*2^n)%nat with (2 ^ S n)%nat.
      exact l1. reflexivity.
    + pose proof (CRlt_trans _ _ _ c1 c) as H.
      (* Integral on [BinarySubdiv a b (S n) j, BinarySubdiv a b (S n) (S j)]
         lower than integral on
         [BinarySubdiv a b n (i-1), BinarySubdiv a b n i]  *)
      destruct (le_lt_dec (S (S j)) (2*i)).
      * exfalso.
        exact (StepApproxDiscretizeRefineIncr
                 f fInt a b eta aPos ltab aeta beta n (S j) i l1 H).
      * apply le_S_n in l1. unfold BinarySubdiv. rewrite CRplus_assoc.
        apply CRplus_le_compat_l.
        do 2 rewrite <- (CRmult_comm (b-a)), CRmult_assoc.
        rewrite <- CRmult_plus_distr_l.
        rewrite <- (CRmult_1_l (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) (S n))).
        rewrite <- CRmult_plus_distr_r.
        simpl (CRpow (CR_of_Q (RealT (ElemFunc IS)) (/ 2)) (S n)).
        apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltab.
        rewrite <- CRmult_assoc. apply CRmult_le_compat_r.
        apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
        rewrite <- CR_of_Q_one, <- CR_of_Q_plus, <- CR_of_Q_mult. apply CR_of_Q_le.
        apply Qle_shift_div_l. reflexivity.
        unfold Qplus, Qmult, Qle, Qnum, Qden.
        do 4 rewrite Z.mul_1_r.
        replace 2%Z with (Z.of_nat 2). rewrite <- Nat2Z.inj_mul.
        replace 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add.
        apply Nat2Z.inj_le. rewrite Nat.add_comm, Nat.mul_comm. exact l1.
        reflexivity. reflexivity.
Qed.

Lemma FindCrossingPointDecr
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a b eta alpha : CRcarrier (RealT (ElemFunc IS)))
      (aPos : 0 < a) (ltab : a < b)
      (aeta : 0 < a - eta < a) (beta : 0 < b < b + eta)
      (n i j : nat),
    ((i <= 2 ^ n)%nat *
     ((i = (2 ^ n)%nat) +
      (StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n (S i) < alpha)) *
     (alpha < StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n i))
    -> ((j <= 2 ^ S n)%nat *
       ((j = (2 ^ S n)%nat) +
        (StepApproxDiscretize
           f fInt a b eta aPos ltab aeta beta (S n) (S j) < alpha)) *
       (alpha < StepApproxDiscretize f fInt a b eta aPos ltab aeta beta (S n) j))
    -> BinarySubdiv a b (S n) j
      <= BinarySubdiv a b n i + (b-a) * CRpow (CR_of_Q _ (1#2)) n.
Proof.
  intros. destruct H,H0,p,p0. destruct s.
  - subst i. rewrite BinarySubdivRight.
    apply (CRle_trans _ (b+0)). rewrite CRplus_0_r.
    apply BinarySubdivInside. apply CRlt_asym, ltab. exact l0.
    apply CRplus_le_compat_l. apply CRmult_le_0_compat.
    apply CRlt_asym, CRlt_minus, ltab. apply pow_le.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    apply CRlt_asym, ltab.
  - destruct s0.
    subst j. rewrite BinarySubdivRight. 2: apply CRlt_asym, ltab.
    destruct (le_lt_dec (2^n) i).
    + unfold BinarySubdiv.
      apply (CRplus_le_reg_l (-a)).
      rewrite <- CRplus_assoc, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite <- (CRmult_comm (b-a)), <- (CRmult_1_r (-a+b)).
      rewrite CRmult_assoc, <- CRmult_plus_distr_l, CRplus_comm.
      apply CRmult_le_compat_l.
      apply CRlt_asym, CRlt_minus, ltab.
      rewrite <- (CRmult_1_l (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)).
      rewrite <- CRmult_plus_distr_r.
      apply (CRmult_le_reg_r (CRpow (CR_of_Q _ (Z.of_nat 2 # 1)) n)).
      apply pow_lt. apply CR_of_Q_pos. reflexivity.
      rewrite CRmult_1_l, CRmult_assoc, pow_mult.
      rewrite (pow_proper (CR_of_Q (RealT (ElemFunc IS)) (/ 2) *
                           CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat 2 # 1)) 1).
      rewrite pow_one, <- pow_nat, CRmult_1_r.
      rewrite <- CR_of_Q_one, <- CR_of_Q_plus.
      apply CR_of_Q_le.
      unfold Qplus, Qle, Qnum, Qden. do 4 rewrite Z.mul_1_r.
      replace 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add.
      apply Nat2Z.inj_le. apply (le_trans _ i _ l1).
      rewrite Nat.add_comm. apply le_S, le_refl.
      reflexivity.
      rewrite <- CR_of_Q_mult, <- CR_of_Q_one. apply CR_of_Q_morph.
      reflexivity.
    + exfalso. pose proof (CRlt_trans _ _ _ c1 c0).
      apply (StepApproxDiscretizeRefineDecr
               f fInt a b eta aPos ltab aeta beta n (2^S n) (S i)).
      2: exact H. unfold lt in l1. apply Nat.mul_le_mono_nonneg_l.
      apply le_0_n. exact l1.
    + pose proof (CRlt_trans _ _ _ c1 c0) as H.
      (* Integral on [BinarySubdiv a b (S n) j, BinarySubdiv a b (S n) (S j)]
         lower than integral on
         [BinarySubdiv a b n (i-1), BinarySubdiv a b n i]  *)
      destruct (le_lt_dec (2*S i) j).
      * exfalso.
        exact (StepApproxDiscretizeRefineDecr
                 f fInt a b eta aPos ltab aeta beta n j (S i) l1 H).
      * unfold BinarySubdiv. rewrite CRplus_assoc.
        apply CRplus_le_compat_l.
        do 2 rewrite <- (CRmult_comm (b-a)), CRmult_assoc.
        rewrite <- CRmult_plus_distr_l.
        rewrite <- (CRmult_1_l (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)).
        rewrite <- CRmult_plus_distr_r.
        simpl (CRpow (CR_of_Q (RealT (ElemFunc IS)) (/ 2)) (S n)).
        apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltab.
        rewrite <- CRmult_assoc. apply CRmult_le_compat_r.
        apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
        rewrite <- CR_of_Q_one, <- CR_of_Q_plus, <- CR_of_Q_mult. apply CR_of_Q_le.
        apply Qle_shift_div_r. reflexivity.
        unfold Qplus, Qmult, Qle, Qnum, Qden.
        do 4 rewrite Z.mul_1_r.
        replace 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add. 2: reflexivity.
        replace 2%Z with (Z.of_nat 2). rewrite <- Nat2Z.inj_mul. 2: reflexivity.
        apply Nat2Z.inj_le. apply le_S_n.
        apply (le_trans _ _ _ l1).
        rewrite (Nat.mul_comm (i+1)). apply le_S. rewrite Nat.add_comm.
        apply le_refl.
Qed.

Lemma FindCrossingPointThreasholdDecr
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a b eta alpha gamma : CRcarrier (RealT (ElemFunc IS)))
      (aPos : 0 < a) (ltab : a < b)
      (aeta : 0 < a - eta < a) (beta : 0 < b < b + eta)
      (n i j : nat),
    alpha <= gamma
    -> ((i <= 2 ^ n)%nat *
       ((i = (2 ^ n)%nat) +
        (StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n (S i) < alpha)) *
       (alpha < StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n i))
    -> ((j <= 2 ^ n)%nat *
       ((j = (2 ^ n)%nat) +
        (StepApproxDiscretize
           f fInt a b eta aPos ltab aeta beta n (S j) < gamma)) *
       (gamma < StepApproxDiscretize f fInt a b eta aPos ltab aeta beta n j))
    -> le j i.
Proof.
  intros. destruct H0, H1, p, p0.
  destruct s, s0.
  - subst i. rewrite e0. apply le_refl.
  - subst i. exact l0.
  - subst j. clear l0.
    apply (CRlt_le_trans _ _ _ c1) in H.
    apply (CRlt_trans _ _ _ H) in c0. clear H c1 c.
    unfold StepApproxDiscretize in c0.
    destruct (2^n)%nat eqn:des. apply le_0_n. rewrite <- des.
    destruct (le_lt_dec (S (S n0)) (S n0)). exfalso.
    exact (le_not_lt _ _ l0 (le_refl _)).
    destruct (le_lt_dec (S (S n0)) (S i)).
    + apply le_S_n in l1. pose proof (le_antisym _ _ l l1).
      subst i. rewrite <- des. apply le_refl.
    + clear l0. apply le_S_n, le_S_n in l1. clear l. exfalso.
      apply (StepApproxIntegralIncr
               f fInt
               (BinarySubdiv a b n i) (BinarySubdiv a b n (S i))
               (BinarySubdiv a b n n0) (BinarySubdiv a b n (S n0))
               (BinarySubdivIncr a b n i (aPos, ltab))
               (BinarySubdivIncr a b n n0 (aPos, ltab))).
      3: exact c0. clear c0.
      apply CRplus_le_compat_l. do 2 rewrite CRmult_assoc.
      apply CRmult_le_compat_r. apply CRlt_asym, CRmult_lt_0_compat.
      apply CRlt_minus, ltab. apply pow_lt, CR_of_Q_pos. reflexivity.
      apply CR_of_Q_le. unfold Qle, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, l1.
      apply CRplus_le_compat_l. do 2 rewrite CRmult_assoc.
      apply CRmult_le_compat_r. apply CRlt_asym, CRmult_lt_0_compat.
      apply CRlt_minus, ltab. apply pow_lt, CR_of_Q_pos. reflexivity.
      apply CR_of_Q_le. unfold Qle, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, le_n_S, l1.
  - apply (CRlt_le_trans _ _ _ c1) in H.
    apply (CRlt_trans _ _ _ H) in c0. unfold StepApproxDiscretize in c0.
    destruct j. apply le_0_n.
    destruct (le_lt_dec (S (2 ^ n)) (S j)).
    exfalso. apply le_S_n in l1. exact (le_not_lt _ _ l1 l0).
    destruct (le_lt_dec (S (2 ^ n)) (S i)).
    apply le_S_n in l1. apply le_S_n in l2. exact (le_trans _ _ _ l1 l2).
    destruct (le_lt_dec (S j) i). exact l3. exfalso.
    apply (StepApproxIntegralIncr
             f fInt
             (BinarySubdiv a b n i) (BinarySubdiv a b n (S i))
             (BinarySubdiv a b n j) (BinarySubdiv a b n (S j))
             (BinarySubdivIncr a b n i (aPos, ltab))
             (BinarySubdivIncr a b n j (aPos, ltab))).
    3: exact c0. apply le_S_n in l3.
    apply CRplus_le_compat_l. do 2 rewrite CRmult_assoc.
    apply CRmult_le_compat_r. apply CRlt_asym, CRmult_lt_0_compat.
    apply CRlt_minus, ltab. apply pow_lt, CR_of_Q_pos. reflexivity.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, l3.
    apply CRplus_le_compat_l. do 2 rewrite CRmult_assoc.
    apply CRmult_le_compat_r. apply CRlt_asym, CRmult_lt_0_compat.
    apply CRlt_minus, ltab. apply pow_lt, CR_of_Q_pos. reflexivity.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, l3.
Qed.

Lemma diff_series_cv_maj
  : forall {R : ConstructiveReals}
      (un vn : nat -> CRcarrier R) (s : CRcarrier R),
    (* skip 0 *)
    (forall n:nat, CRabs R (un (S n) - un n) <= vn n)
    -> series_cv vn s
    -> { l : CRcarrier R & prod (CR_cv R un l) (l <= s + CRabs R (un O)) }.
Proof.
  intros.
  destruct (series_cv_maj (fun n:nat => match n with
                                   | O => un O
                                   | S p => un n - un p end)
                          (fun n:nat => match n with
                                   | O => CRabs R (un O)
                                   | S p => vn p end)
                          (s + CRabs R (un O))) as [l lcv].
  - intro n. destruct n. apply CRle_refl. apply H.
  - intro p. specialize (H0 p) as [n ncv].
    exists (S n). intros. destruct i. exfalso; inversion H0.
    rewrite decomp_sum. simpl. unfold CRminus.
    rewrite CRplus_comm, CRopp_plus_distr, CRplus_assoc.
    rewrite <- (CRplus_assoc (-CRabs R (un O))), CRplus_opp_l, CRplus_0_l.
    rewrite CRplus_comm. apply ncv. apply le_S_n, H0.
    apply le_n_S, le_0_n.
  - exists l. split. 2: exact (snd lcv).
    apply (CR_cv_eq _ (CRsum (fun n : nat => match n with
                          | 0%nat => un 0%nat
                          | S p => un n - un p
                                           end))).
    + induction n. reflexivity. simpl. rewrite IHn.
      rewrite CRplus_comm. unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
    + exact (fst lcv).
Qed.

Lemma StepApproxProofIrrel
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (s t : CRcarrier (RealT (ElemFunc IS))) (ltst ltst2 : 0 < s < t),
    Integral (StepApproxIntegrable f s t ltst fInt)
    == Integral (StepApproxIntegrable f s t ltst2 fInt).
Proof.
  intros. apply IntegralExtensional.
  intros. simpl. destruct xdf, xdg.
  apply (CRmult_eq_reg_l (t-s)). right. apply CRlt_minus, ltst.
  rewrite <- CRmult_assoc, CRinv_r, CRmult_1_l, (CRmult_comm (t-s)).
  apply (CRmult_eq_reg_l (t-s)). right. apply CRlt_minus, ltst.
  rewrite <- CRmult_assoc, <- CRmult_assoc, CRinv_r, CRmult_1_l.
  rewrite CRmult_comm. rewrite (DomainProp f x d2 d), (DomainProp f x d1 d).
  rewrite (DomainProp f x d0 d). reflexivity.
Qed.

(* There are at most q+1 points with jumps bigger than epsilon,
   s0, ..., sq.
   To search jump points, we throw missiles from a to b with increasing speeds
   epsilon * (k / q),  k=0..q
   Jump points are barriers that take down some of the missile speed,
   it will continue going towards b as long as it has positive speed.
   When there are no jump points (f = 0), all points sk's will be equal to b. *)
Lemma FindJumpPointsFinite
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a b alpha epsilon : CRcarrier (RealT (ElemFunc IS)))
      (aPos : 0 < a) (ltab : a < b) (epsPos : 0 < epsilon) (q : nat),
    alpha <= CR_of_Q _ (Z.of_nat q # 1) * epsilon
    -> q <> O
    -> StepApproxBound f fInt a b alpha (CRlt_asym a b ltab)
    -> { s : nat -> CRcarrier (RealT (ElemFunc IS))
      | (s O == a) /\ (forall k:nat, le q k -> s k == b)
        /\ (forall k:nat, s k <= s (S k))
        /\ (forall k:nat, StepApproxBoundOpen f fInt (s k) (s (S k)) epsilon) }.
Proof.
  intros IS f fInt a b alpha epsilon aPos ltab epsPos q H qnz H0.
  destruct H0 as [ext c].
  pose (StepApproxDiscretize
          f fInt a b (ext_eta ext) aPos ltab
          (left_ordered ext) (pair (CRlt_trans _ _ _ aPos ltab) (right_ordered ext)))
    as Fni.

  (* We define the q numbers sk as limits of sequences. *)
  (* Define the non-negative sequence of jumps *)
  (* pose (fun n i : nat => Fni n O - Fni n i) as Sni. *)
  destruct (CRuncountableDiag3
              (fun n i k => (Fni n O - Fni n i)
                         * CR_of_Q _ (Z.of_nat q # Pos.of_nat (S k)))
              _ alpha c)
    as [epsilonPrime H0]. destruct H0.
  assert (0 < epsilonPrime) as epsilonPrimePos.
  { apply (CRle_lt_trans _ (Integral (StepApproxIntegrable f (a - ext_eta ext) a (left_ordered ext) fInt) - Integral
        (StepApproxIntegrable f b (b + ext_eta ext)
           (IntExtRightPos ext (CRlt_asym a b ltab), right_ordered ext) fInt))).
    2: apply p.
    apply (CRplus_le_reg_r ( Integral
    (StepApproxIntegrable f b (b + ext_eta ext)
                          (IntExtRightPos ext (CRlt_asym a b ltab), right_ordered ext) fInt))).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_0_l.
    apply StepApproxIntegralIncr.
    apply (CRle_trans _ a). apply CRlt_asym, ext. apply CRlt_asym, ltab.
    apply (CRle_trans _ b). apply CRlt_asym, ltab. apply CRlt_asym, ext. }
  assert (forall n k:nat,
             Fni n O - CR_of_Q _ (Z.of_nat (S k) # Pos.of_nat q) * epsilonPrime
             < Fni n O) as H0.
  { intros. unfold CRminus. apply (CRplus_lt_reg_l _ (-Fni n O)).
    apply (CRlt_le_trans _ (CRzero _)).
    2: apply CRplus_opp_l.
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, <- CRopp_0.
    apply CRopp_gt_lt_contravar.
    apply CRmult_lt_0_compat. apply CR_of_Q_pos. reflexivity.
    exact epsilonPrimePos. }
  assert (forall n k i : nat,
        CRapart (RealT (ElemFunc IS))
    (Fni n 0%nat -
     CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (S k) # Pos.of_nat q) * epsilonPrime)
    (Fni n i)).
  { intros.
    apply (CRplus_appart_reg_r (CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (S k) # Pos.of_nat q) * epsilonPrime)).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    apply (CRplus_appart_reg_l (-(Fni n i))).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_comm.
    specialize (c0 n i k).
    apply (CRmult_appart_reg_l
             (CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat q # Pos.of_nat (S k)))).
    apply CR_of_Q_pos. destruct q. exfalso; exact (qnz (eq_refl O)).
    reflexivity.
    rewrite <- CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace
      ((Z.of_nat q # Pos.of_nat (S k)) * (Z.of_nat (S k) # Pos.of_nat q))%Q
      with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_l, CRmult_comm.
    destruct c0. right. exact c0. left. exact c0.
    unfold Qmult, Qeq, Qnum, Qden.
    rewrite Z.mul_1_l, Z.mul_1_r, Z.mul_comm.
    rewrite Pos2Z.inj_mul. apply f_equal2.
    simpl (Z.of_nat (S k)). apply f_equal.
    rewrite Pos.of_nat_succ. reflexivity.
    destruct q. exfalso; exact (qnz (eq_refl O)).
    simpl (Z.of_nat (S q)). apply f_equal.
    rewrite Pos.of_nat_succ. reflexivity. }
  pose proof (fun (n k:nat)
        => FindCrossingPoint
            (Fni n) (2 ^ n) (* gives 2^n + 1 possible indices,
                               as many as the numbers of points in the
                               nth binary subdivision of [a,b] *)
            (Fni n O - CR_of_Q _ (Z.of_nat (S k) # Pos.of_nat q) * epsilonPrime)
            (fun i:nat => StepApproxDiscretizeDecr
               f fInt a b (ext_eta ext) aPos ltab (left_ordered ext)
               (pair (CRlt_trans _ _ _ aPos ltab) (right_ordered ext))
               n i (S i) (le_S i i (le_refl i)))
            (H1 n k) (H0 n k)) as H2.
  clear H1. clear H0.
  pose (fun (n k:nat) => let (i,_) := H2 n k in BinarySubdiv a b n i) as snk.
  assert (forall n k:nat, CRabs _ (snk (S n) k - snk n k)
                   <= (b-a) * CRpow (CR_of_Q _ (1#2)) n).
  { intros n k. unfold snk.
    destruct (H2 n k), (H2 (S n) k). apply CRabs_le. split.
    - pose proof (FindCrossingPointIncr
             f fInt a b (ext_eta ext)
             (Fni n O - CR_of_Q _ (Z.of_nat (S k) # Pos.of_nat q) * epsilonPrime)
             aPos ltab (left_ordered ext)
             (pair (CRlt_trans _ _ _ aPos ltab) (right_ordered ext))
             _ _ _ p0 p1).
      apply (CRplus_le_reg_r (BinarySubdiv a b n x)). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply (CRplus_le_reg_l
               ((b - a) * CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)).
      rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l, CRplus_comm.
      apply (CRle_trans _ _ _ H0). apply CRplus_le_compat_l.
      apply CRmult_le_compat_l. apply CRlt_asym, CRlt_minus, ltab.
      rewrite <- (CRmult_1_l (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)).
      simpl. apply CRmult_le_compat_r. apply pow_le, CRlt_asym, CR_of_Q_pos.
      reflexivity. rewrite <- CR_of_Q_one. apply CR_of_Q_le. discriminate.
    - pose proof (FindCrossingPointDecr
             f fInt a b (ext_eta ext)
             (Fni n O - CR_of_Q _ (Z.of_nat (S k) # Pos.of_nat q) * epsilonPrime)
             aPos ltab (left_ordered ext)
             (pair (CRlt_trans _ _ _ aPos ltab) (right_ordered ext))
             _ _ _ p0 p1).
      apply (CRplus_le_reg_r (BinarySubdiv a b n x)).
      unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_comm.
      exact H0. }
  assert (series_cv
            (fun n : nat => (b - a) * CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)
            (CR_of_Q _ 2 * (b-a))).
  { apply (series_cv_eq
             (fun n : nat => CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n * (b-a))).
    intro n. apply CRmult_comm. apply series_cv_scale. apply GeoHalfTwo. }
  pose proof (fun (k:nat) => diff_series_cv_maj
                          (fun n => snk n k)
                          (fun n => (b - a) * CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)
                          (CR_of_Q _ 2 * (b-a)) (fun n => H0 n k) H1).
  pose (fun k:nat => match k with
             | O => a (* necessary special case at a, because all missiles
                        go to b when f=0 *)
             | S i => let (l,_) := H3 i in l
             end) as sk.
  exists sk.
  assert (forall k:nat, le q k -> sk k == b) as lastB.
  { intros. unfold sk. destruct k.
    exfalso. inversion H4. rewrite H5 in qnz.
    exact (qnz (eq_refl _)).
    destruct (H3 k) as [x p0]. destruct p0. clear c2.
    apply (CR_cv_unique (fun n : nat => snk n k) _ _ c1). clear c1 x.
    apply (CR_cv_eq _ (fun _ : nat => b)). 2: apply CR_cv_const.
    intro n. unfold snk.
    destruct (H2 n k). destruct p0, p0.
    destruct s.
    - rewrite e.
      rewrite BinarySubdivRight. reflexivity. apply CRlt_asym, ltab.
    - exfalso. clear c1. contradict c2.
      apply (CRle_trans _ (Fni n (S (2^n)))).
      2: apply StepApproxDiscretizeDecr, le_n_S, l.
      apply (CRle_trans _ ( Fni n 0%nat - 1 * epsilonPrime)).
      apply CRplus_le_compat_l, CRopp_ge_le_contravar.
      apply CRmult_le_compat_r. apply CRlt_asym, epsilonPrimePos.
      rewrite <- CR_of_Q_one. apply CR_of_Q_le.
      unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_l.
      simpl (Z.of_nat (S k)). apply Pos2Z.pos_le_pos.
      rewrite Pos.of_nat_succ. apply Pos2Nat.inj_le.
      rewrite Nat2Pos.id, Nat2Pos.id. exact H4.
      discriminate. exact qnz. rewrite CRmult_1_l.
      apply (CRplus_le_reg_r epsilonPrime).
      unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply (CRplus_le_reg_l (-Fni n (S (2^n)))).
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_comm.
      destruct p. unfold Fni, StepApproxDiscretize.
      destruct (le_lt_dec (S (2 ^ n)) (S (2 ^ n))).
      rewrite (StepApproxProofIrrel
                 f fInt _ _
                 (CRlt_trans 0 a b aPos ltab, right_ordered ext)
                 (IntExtRightPos ext (CRlt_asym a b ltab), right_ordered ext) ).
      apply CRlt_asym, c1.
      exfalso; exact (lt_not_le _ _ l0 (le_refl _)). }
  assert (forall k : nat, sk k <= sk (S k)) as skIncr.
  { unfold sk. intros k. destruct k.
    - destruct (H3 O).
      apply (CR_cv_bound_down (fun n : nat => snk n 0%nat) _ _ O).
      intros. unfold snk. destruct (H2 n O).
      apply BinarySubdivInside. apply CRlt_asym, ltab.
      apply (fst p1). exact (fst p0).
    - destruct (H3 k), (H3 (S k)).
      apply (CR_cv_le (fun n : nat => snk n k) (fun n : nat => snk n (S k))).
      2: exact (fst p0). 2: exact (fst p1). intro n.
      unfold snk. destruct (H2 n k), (H2 n (S k)).
      apply CRplus_le_compat_l. rewrite CRmult_assoc, CRmult_assoc.
      apply CRmult_le_compat_r. apply CRmult_le_0_compat.
      apply CRlt_asym, CRlt_minus, ltab. apply pow_le.
      apply CRlt_asym, CR_of_Q_pos. reflexivity. apply CR_of_Q_le.
      unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le.
      apply (FindCrossingPointThreasholdDecr
               f fInt a b (ext_eta ext)
               (Fni n 0%nat -
                CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (S (S k)) # Pos.of_nat q) *
                epsilonPrime)
               (Fni n 0%nat -
                CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (S k) # Pos.of_nat q) * epsilonPrime)
               aPos ltab (left_ordered ext)
               (CRlt_trans 0 a b aPos ltab, right_ordered ext) n).
      2: exact p3. 2: exact p2.
      apply CRplus_le_compat_l, CRopp_ge_le_contravar.
      apply CRmult_le_compat_r. apply CRlt_asym, epsilonPrimePos.
      apply CR_of_Q_le. unfold Qle, Qnum, Qden.
      apply Z.mul_le_mono_nonneg_r. discriminate. apply Nat2Z.inj_le.
      apply le_S, le_refl. }
  split. 2: split. 3: split.
  - reflexivity.
  - exact lastB.
  - exact skIncr.
  - (* No jumps between jump points. *)
    intros k x y u v ltxy ltuv H4 H5 H6.
    destruct (le_lt_dec q k) as [l | ltkq].
    contradict H6.
    apply (CRle_trans _ b). apply lastB. apply le_S, l.
    apply (CRle_trans _ u). 2: apply CRlt_asym, (snd ltuv).
    apply (CRle_trans _ y). 2: exact H5.
    apply (CRle_trans _ x). 2: apply CRlt_asym, (snd ltxy).
    rewrite <- (lastB k). apply CRlt_asym, H4. exact l.
    assert (CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat 1 # Pos.of_nat q) * epsilonPrime
            < epsilon).
    { apply (CRmult_lt_reg_l (CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat q # 1))).
      apply CR_of_Q_pos. destruct q. exfalso; exact (qnz (eq_refl _)).
      reflexivity. apply (CRlt_le_trans _ alpha). 2: exact H.
      apply (CRle_lt_trans _ epsilonPrime). 2: exact (snd p).
      rewrite <- CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((Z.of_nat q # 1) * (Z.of_nat 1 # Pos.of_nat q))%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_l. apply CRle_refl.
      unfold Qmult, Qeq, Qnum, Qden. simpl. do 2 rewrite Z.mul_1_r.
      destruct q. exfalso; exact (qnz (eq_refl _)). simpl (Z.of_nat (S q)).
      apply f_equal. apply (Pos.of_nat_succ). }
    destruct (CR_cv_open_below
                (fun n => snk n k + (CRpow (CR_of_Q _ (1#2)) n)*(-(b-a)))
                v (sk (S k))) as [m mcv].
    apply (CR_cv_proper _ (sk (S k) + 0)). 2: apply CRplus_0_r.
    apply CR_cv_plus. unfold sk.
    destruct (H3 k). exact (fst p0).
    apply (CR_cv_proper _ (0 * (-(b-a)))). apply CR_cv_scale.
    apply GeoCvZero. apply CRmult_0_l. exact H6.
    destruct k.
    + (* First segment, starting at a *)
      apply (CRle_trans _ (Fni m O - Fni m (let (i, _) := H2 m O in i))).
      unfold sk in H4.
      apply CRplus_le_compat. apply StepApproxIntegralIncr.
      apply (CRle_trans _ a). apply CRlt_asym, (snd (left_ordered ext)).
      apply CRlt_asym, H4. apply (CRle_trans _ x).
      apply CRlt_asym, H4. apply CRlt_asym, (snd ltxy).
      apply CRopp_ge_le_contravar. unfold Fni.
      specialize (mcv m (le_refl m)). unfold snk in mcv.
      destruct (H2 m O), p0, p0. unfold StepApproxDiscretize. destruct x0.
      exfalso. contradict mcv. apply (CRle_trans _ (a+0)).
      unfold BinarySubdiv.
      rewrite CR_of_Q_zero, CRmult_0_l, CRmult_0_l, CRplus_assoc.
      apply CRplus_le_compat_l.
      rewrite CRplus_0_l, <- CRopp_mult_distr_r, <- CRopp_0.
      apply CRopp_ge_le_contravar, CRmult_le_0_compat.
      apply pow_le. apply CRlt_asym, CR_of_Q_pos. reflexivity.
      apply CRlt_asym, CRlt_minus, ltab.
      rewrite CRplus_0_r. apply CRlt_asym.
      apply (CRlt_trans _ _ _ H4), (CRlt_trans _ _ _ (snd ltxy)).
      apply (CRle_lt_trans _ _ _ H5), (snd ltuv).
      destruct (le_lt_dec (S (2 ^ m)) (S x0)).
      exfalso. apply le_S_n in l0. exact (lt_not_le _ _ l l0).
      assert (v <= BinarySubdiv a b m x0).
      { apply (CRle_trans _ (BinarySubdiv a b m (S x0) +
                             CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) m * - (b - a))).
        apply CRlt_asym, mcv. rewrite <- BinarySubdivNext.
        rewrite <- CRopp_mult_distr_r, CRplus_assoc, CRplus_opp_r.
        rewrite CRplus_0_r. apply CRle_refl. }
      apply StepApproxIntegralIncr. clear l0 c1 s.
      apply (CRle_trans _ v). apply CRlt_asym, (snd ltuv). exact H8.
      apply (CRle_trans _ _ _ H8). apply CRplus_le_compat_l.
      rewrite CRmult_assoc, CRmult_assoc. apply CRmult_le_compat_r.
      apply CRmult_le_0_compat.
      apply CRlt_asym, CRlt_minus, ltab.
      apply pow_le. apply CRlt_asym, CR_of_Q_pos. reflexivity.
      apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
      apply Nat2Z.inj_le, le_S, le_refl.
      destruct (H2 m O), p0, p0.
      apply (CRplus_le_reg_r (Fni m x0)). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply (CRplus_le_reg_r (-
       (CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat 1 # Pos.of_nat q) * epsilonPrime))).
      apply (CRle_trans _ (Fni m x0) _ (CRlt_asym _ _ c1)).
      rewrite (CRplus_comm epsilon), <- (CRplus_0_r (Fni m x0)).
      rewrite CRplus_assoc, CRplus_assoc.
      apply CRplus_le_compat_l. rewrite CRplus_0_l.
      apply CRlt_asym, CRlt_minus, H7.
    + destruct (CR_cv_open_above
                  (fun n => snk n k + (CRpow (CR_of_Q _ (1#2)) n)*(b-a))
                  x (sk (S k))) as [n ncv].
      2: exact H4.
      apply (CR_cv_proper _ (sk (S k) + 0)). 2: apply CRplus_0_r.
      apply CR_cv_plus. unfold sk.
      destruct (H3 k), p0. exact c1.
      apply (CR_cv_proper _ (0 * (b-a))). apply CR_cv_scale.
      apply GeoCvZero. apply CRmult_0_l.
      specialize (ncv (max n m) (Nat.le_max_l _ _)).
      specialize (mcv (max n m) (Nat.le_max_r _ _)).
      rewrite <- CRopp_mult_distr_r in mcv.
      apply (CRle_trans
               _ (Fni (max n m) (let (i,_) := H2 (max n m) k in S i)
                  - Fni (max n m) (let (i, _) := H2 (max n m) (S k) in i))).
      * assert (forall i j:nat, le i j -> sk i <= sk j).
        { induction j. intros. inversion H8. apply CRle_refl.
          intros. apply Nat.le_succ_r in H8. destruct H8.
          apply (CRle_trans _ (sk j)). exact (IHj H8).
          apply skIncr. subst i. apply CRle_refl. }
        apply CRplus_le_compat.
        (* Interval [x,y] *)
        clear mcv.
        unfold Fni, StepApproxDiscretize. unfold snk in ncv.
        destruct (H2 (max n m) k) as [x0 p0].
        destruct (le_lt_dec (S (2 ^ max n m)) (S x0)).
        destruct p0, p0. apply le_S_n in l.
        apply (le_antisym _ _ l0) in l. subst x0. (* x0 = 2 ^ max n m *)
        clear l0 s c1.
        contradict ncv. apply (CRle_trans _ (b+0)).
        rewrite CRplus_0_r. apply (CRle_trans _ y _ (CRlt_asym _ _ (snd ltxy))).
        apply (CRle_trans _ u _ H5).
        apply (CRle_trans _ v _ (CRlt_asym _ _ (snd ltuv))).
        apply (CRle_trans _ _ _ (CRlt_asym _ _ H6)).
        apply (CRle_trans _ (sk q)).
        apply H8. exact ltkq. apply lastB. apply le_refl.
        rewrite BinarySubdivRight. apply CRplus_le_compat_l.
        apply CRlt_asym, CRmult_lt_0_compat.
        apply pow_lt, CR_of_Q_pos. reflexivity.
        apply CRlt_minus, ltab. apply CRlt_asym, ltab.
        rewrite BinarySubdivNext in ncv. apply StepApproxIntegralIncr.
        apply le_S_n in l. destruct p0, p0. clear l0.
        apply (CRle_trans _ (BinarySubdiv a b (max n m) (S x0))).
        apply CRlt_asym, BinarySubdivIncr. exact (pair aPos ltab).
        apply CRlt_asym, ncv.
        apply (CRle_trans _ x). apply CRlt_asym, ncv.
        apply CRlt_asym, (snd ltxy).
        (* Interval [u,v] *)
        clear ncv. apply CRopp_ge_le_contravar.
        unfold Fni, StepApproxDiscretize. unfold snk in mcv.
        destruct (H2 (max n m) (S k)), p0, p0. destruct x0.
        clear l c1. contradict mcv.
        apply (CRle_trans _ (a-0)). unfold BinarySubdiv, CRminus.
        rewrite CRplus_assoc. apply CRplus_le_compat_l.
        rewrite CR_of_Q_zero, CRmult_0_l, CRmult_0_l, CRplus_0_l.
        apply CRopp_ge_le_contravar.
        apply CRlt_asym, CRmult_lt_0_compat.
        apply pow_lt, CR_of_Q_pos. reflexivity.
        apply CRlt_minus, ltab. unfold CRminus. rewrite CRopp_0, CRplus_0_r.
        apply (CRle_trans _ (sk (S k))). apply (H8 O (S k)), le_0_n.
        apply (CRle_trans _ x _ (CRlt_asym _ _ H4)).
        apply (CRle_trans _ y _ (CRlt_asym _ _ (snd ltxy))).
        apply (CRle_trans _ u _ H5).
        apply CRlt_asym, (snd ltuv).
        destruct (le_lt_dec (S (2 ^ max n m)) (S x0)).
        apply le_S_n in l0.
        exfalso. exact (lt_not_le _ _ l l0).
        rewrite <- BinarySubdivNext, CRplus_assoc, CRplus_opp_r, CRplus_0_r in mcv.
        apply StepApproxIntegralIncr.
        apply CRlt_asym, (CRlt_trans _ v _ (snd ltuv) mcv).
        apply CRlt_asym, (CRlt_trans _ _ _ mcv). apply BinarySubdivIncr.
        exact (pair aPos ltab).
      * destruct (H2 (max n m) k) as [x0 p0], (H2 (max n m) (S k)) as [x1 p1].
        destruct p0, p1, p0, p1. destruct s. subst x0.
        apply (CRplus_le_reg_r (Fni (max n m) x1)).
        unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
        apply (CRle_trans _ (0 + Fni (max n m) x1)).
        rewrite CRplus_0_l.
        apply StepApproxDiscretizeDecr. apply le_S, l0.
        apply CRplus_le_compat_r. apply CRlt_asym, epsPos.
        apply (CRle_trans
                 _ (Fni (Init.Nat.max n m) 0%nat -
                    CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (S k) # Pos.of_nat q)
                    * epsilonPrime
                    - (Fni (Init.Nat.max n m) 0%nat -
                       CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (S (S k)) # Pos.of_nat q) * epsilonPrime))).
        apply CRplus_le_compat. apply CRlt_asym, c3.
        apply CRopp_ge_le_contravar. apply CRlt_asym, c2.
        unfold CRminus.
        rewrite (CRplus_comm (Fni (max n m) O)), CRplus_assoc, CRopp_plus_distr.
        rewrite <- (CRplus_assoc (Fni (max n m) O)), CRplus_opp_r, CRplus_0_l.
        rewrite CRopp_involutive, CRopp_mult_distr_l.
        rewrite <- CRmult_plus_distr_r.
        apply (CRle_trans _ ((CR_of_Q _ (1 # Pos.of_nat q)) * epsilonPrime)).
        apply CRmult_le_compat_r. apply CRlt_asym, epsilonPrimePos.
        rewrite <- CR_of_Q_opp, <- CR_of_Q_plus. apply CR_of_Q_le.
        rewrite Qplus_comm, Qinv_minus_distr.
        unfold Qle, Qnum, Qden. apply Z.mul_le_mono_nonneg_r. discriminate.
        destruct k. discriminate.
        2: apply CRlt_asym, H7.
        rewrite (Z.add_le_mono_r _ _ (Z.of_nat (S (S k)))).
        ring_simplify. replace 1%Z with (Z.of_nat 1).
        rewrite <- Nat2Z.inj_add, Nat.add_comm. apply Z.le_refl.
        reflexivity.
Qed.

Lemma FindInterval {R : ConstructiveReals} (un : nat -> CRcarrier R)
      (x : CRcarrier R) (i j : nat)
  : (forall n:nat, un n <= un (S n))
    -> (forall n:nat, CRapart R x (un n))
    -> un i < x < un j
    -> { k : nat & un k < x < un (S k) }.
Proof.
  intro uIncr.
  assert (forall b : nat, un O <= un b).
  { induction b. apply CRle_refl.
    apply (CRle_trans _ (un b) _ IHb). apply uIncr. }
  induction j.
  - intros. pose proof (CRlt_trans _ _ _ (fst H1) (snd H1)) as H3.
    contradict H3. apply H.
  - intros. specialize (IHj H0).
    destruct (H0 j). exact (IHj (pair (fst H1) c)).
    exists j. exact (pair c (snd H1)).
Qed.

Lemma IntervalOpenEta : forall {R : ConstructiveReals} (a b x : CRcarrier R),
    a < x < b
    -> { eta : CRcarrier R  &  prod (a < x-eta < x) (x < x+eta < b) }.
Proof.
  intros. exists (CRmin (x-a) (b-x) * CR_of_Q R (1#2)).
  split. split.
  apply (CRplus_lt_reg_r (CRmin (x - a) (b - x) * CR_of_Q R (1 # 2))).
  unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
  apply (CRplus_lt_reg_l R (-a)).
  rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
  apply (CRlt_le_trans _ (CRmin (x + - a) (b + - x) * 1)).
  2: rewrite CRmult_1_r, CRplus_comm; apply CRmin_l.
  apply CRmult_lt_compat_l. apply CRmin_lt. apply CRlt_minus, (fst H).
  apply CRlt_minus, (snd H).
  rewrite <- CR_of_Q_one. apply CR_of_Q_lt. reflexivity.
  apply (CRlt_le_trans _ (x+0)). apply CRplus_lt_compat_l.
  rewrite <- CRopp_0. apply CRopp_gt_lt_contravar.
  apply CRmult_lt_0_compat. apply CRmin_lt.
  apply CRlt_minus. exact (fst H). apply CRlt_minus. exact (snd H).
  apply CR_of_Q_pos. reflexivity. rewrite CRplus_0_r. apply CRle_refl.
  split. apply (CRle_lt_trans _ (x+0)). rewrite CRplus_0_r.
  apply CRle_refl. apply CRplus_lt_compat_l. apply CRmult_lt_0_compat.
  apply CRmin_lt. apply CRlt_minus. exact (fst H).
  apply CRlt_minus. exact (snd H). apply CR_of_Q_pos. reflexivity.
  apply (CRplus_lt_reg_l R (-x)).
  rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
  apply (CRle_lt_trans _ ((b - x) * CR_of_Q R (1 # 2))).
  apply CRmult_le_compat_r. rewrite <- CR_of_Q_zero.
  apply CR_of_Q_le. discriminate. apply CRmin_r.
  rewrite CRplus_comm, <- (CRmult_1_r (b + - x)).
  apply CRmult_lt_compat_l. apply CRlt_minus. exact (snd H).
  rewrite <- CR_of_Q_one. apply CR_of_Q_lt. reflexivity.
Qed.

Lemma FindJumpPointsCountable
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
    { s : nat -> CRcarrier (RealT (ElemFunc IS))
    & forall x, 0 < x
           -> (forall n:nat, CRapart _ x (s n))
           -> (forall eps, 0 < eps -> StepApproxBound f fInt x x eps (CRle_refl x)) }.
Proof.
  intros.
  pose (fun (n:nat) => CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S n))) as an.
  pose (fun (n:nat) => CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (2+n) # 1)) as bn.
  assert (forall n:nat, an n < bn n) as ltabn.
  { intro n. unfold an, bn.
    apply (CRle_lt_trans _ (CR_of_Q _ 1)).
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos. apply Pos.le_1_l.
    apply CR_of_Q_lt. unfold Qlt, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. apply (Nat2Z.inj_lt 1 (2+n)).
    apply le_n_S, le_n_S, le_0_n. }
  assert (forall n:nat, 0 < an n) as anPos.
  { intro n. apply CR_of_Q_pos. reflexivity. }
  assert (forall n:nat, 0 < an n - an n * CR_of_Q _ (1#2) < an n) as orderBefore.
  { split. apply (CRlt_le_trans _ (an n * CR_of_Q _ (1#2))).
    apply CRmult_lt_0_compat. exact (anPos n).
    apply CR_of_Q_pos. reflexivity.
    apply (CRplus_le_reg_r (an n * CR_of_Q (RealT (ElemFunc IS)) (1 # 2))).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus.
    setoid_replace ((1 # 2) + (1 # 2))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_r. apply CRle_refl. reflexivity.
    apply (CRle_lt_trans _ (an n * CR_of_Q _ (1#2))).
    apply (CRplus_le_reg_r (an n * CR_of_Q (RealT (ElemFunc IS)) (1 # 2))).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus.
    setoid_replace ((1 # 2) + (1 # 2))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_r. apply CRle_refl. reflexivity.
    rewrite <- (CRmult_1_r (an n)), CRmult_assoc.
    apply CRmult_lt_compat_l. exact (anPos n).
    rewrite CRmult_1_l, <- CR_of_Q_one. apply CR_of_Q_lt. reflexivity. }
  assert (forall n:nat, 0 < bn n < bn n + an n*CR_of_Q _ (1#2)) as orderAfter.
  { split. exact (CRlt_trans _ (an n) _ (anPos n) (ltabn n)).
    apply (CRle_lt_trans _ (bn n + 0)).
    rewrite CRplus_0_r. apply CRle_refl.
    apply CRplus_lt_compat_l. apply CRmult_lt_0_compat.
    exact (anPos n). apply CR_of_Q_pos. reflexivity. }
  pose (fun n:nat => Integral (StepApproxIntegrable
                            f (an n - an n*CR_of_Q _ (1#2)) (an n)
                            (orderBefore n) fInt))
    as intBefore.
  pose (fun n:nat => Integral (StepApproxIntegrable
                            f (bn n) (bn n + an n*CR_of_Q _ (1#2))
                            (orderAfter n) fInt))
    as intAfter.
  pose (fun (n:nat) => let (k,_) := CRup_nat ((1+ intBefore n - intAfter n)
                               * CRinv _ (CR_of_Q _ (1 # Pos.of_nat n))
                                       (inr (CR_of_Q_pos (1 # Pos.of_nat n) (eq_refl _))))
                  in k) as qn.
  assert (forall n:nat, 1 + intBefore n - intAfter n <=
                 CR_of_Q _ (Z.of_nat (qn n) # 1) * CR_of_Q _ (1 # Pos.of_nat n)).
  { intro n. unfold qn.
    destruct ( CRup_nat
            ((1 + intBefore n - intAfter n) *
             CRinv (RealT (ElemFunc IS))
               (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat n))
               (inr (CR_of_Q_pos (1 # Pos.of_nat n) eq_refl)))).
    apply CRlt_asym in c.
    apply (CRmult_le_compat_r (CR_of_Q _ (1 # Pos.of_nat n))) in c.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r in c. exact c.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. }
  assert (forall n:nat, intAfter n <= intBefore n) as orderInt.
  { intro n.
    apply (StepApproxIntegralIncr
             f fInt (an n - an n * CR_of_Q _ (1 # 2)) (an n)
             (bn n) (bn n + an n * CR_of_Q _ (1 # 2))
             (orderBefore n) (orderAfter n)).
    apply (CRle_trans _ (an n)). apply CRlt_asym, orderBefore.
    apply CRlt_asym, ltabn. apply (CRle_trans _ (bn n + 0)).
    rewrite CRplus_0_r. apply CRlt_asym, ltabn.
    apply CRplus_le_compat_l. apply CRlt_asym, CRmult_lt_0_compat.
    exact (anPos n). apply CR_of_Q_pos. reflexivity. }
  assert (forall n:nat, qn n <> O) as qnz.
  { intro n. unfold qn.
    destruct ( CRup_nat
       ((1 + intBefore n - intAfter n) *
        CRinv (RealT (ElemFunc IS))
          (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat n))
          (inr (CR_of_Q_pos (1 # Pos.of_nat n) eq_refl)))).
    apply CRlt_asym in c.
    intro abs. rewrite abs, CR_of_Q_zero in c.
    apply (CRmult_le_compat_r (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat n))) in c.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_0_l in c.
    apply (CRplus_le_compat _ _ _ _ (orderInt n)) in c.
    rewrite CRplus_comm in c. unfold CRminus in c.
    rewrite CRplus_assoc, CRplus_assoc, CRplus_opp_l, CRplus_comm in c.
    rewrite CRplus_assoc in c. apply CRplus_le_reg_l in c.
    rewrite CRplus_0_l in c. apply c. apply CRzero_lt_one.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. }
  assert (forall n:nat, bn n < bn n + an n*CR_of_Q _ (1#2)).
  { intro n. apply (CRle_lt_trans _ (bn n + 0)). rewrite CRplus_0_r.
    apply CRle_refl. apply CRplus_lt_compat_l. apply CRmult_lt_0_compat.
    exact (anPos n). apply CR_of_Q_pos. reflexivity. }
  assert (forall n : nat,
       StepApproxBound f fInt (an n) (bn n) (1 + intBefore n - intAfter n)
                       (CRlt_asym (an n) (bn n) (ltabn n)) ) as intBound.
  { intro n.
    exists (Build_IntervalExtension _ _ _ _ (orderBefore n) (H0 n)).
    simpl. apply (CRle_lt_trans _ (intBefore n - intAfter n)).
    apply CRplus_le_compat. unfold intBefore.
    apply StepApproxIntegralIncr. apply CRle_refl. apply CRle_refl.
    unfold intAfter.
    apply CRopp_ge_le_contravar, StepApproxIntegralIncr.
    apply CRle_refl. apply CRle_refl.
    rewrite <- (CRplus_0_l (intBefore n - intAfter n)).
    unfold CRminus. rewrite CRplus_assoc.
    apply CRplus_lt_compat_r, CRzero_lt_one. }
  pose proof (fun (n:nat) => FindJumpPointsFinite
                    f fInt (an n) (bn n) (1 + intBefore n - intAfter n)
                    (CR_of_Q _ (1 # Pos.of_nat n)) (anPos n) (ltabn n)
                    (CR_of_Q_pos (1 # Pos.of_nat n) (eq_refl _))
                    (qn n) (H n) (qnz n) (intBound n)).
  exists (diagSeq (fun n k => let (s,_) := H1 n in s k)).
  intros.
  assert (forall n k : nat, CRapart _ x (let (s, _) := H1 n in s k)).
  { intros. specialize (H3 (diagPlane n k)). unfold diagSeq in H3.
    rewrite diagPlaneInject in H3. exact H3. }
  clear H3.
  destruct (CRup_nat (CRinv _ eps (inr H4))) as [n nmaj].
  (* Locate x in an open interval ]an p, bn p[ with n <= p *)
  assert (CR_cv _ an 0) as stepCv.
  { unfold an. intro p. exists (Pos.to_nat p). intros. unfold CRminus.
    rewrite CRopp_0, CRplus_0_r. rewrite CRabs_right.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply (le_trans _ _ _ H3).
    apply le_S, le_refl. discriminate.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. }
  destruct (CR_cv_open_above an x 0 stepCv H2) as [i imaj].
  destruct (CRup_nat x) as [j jmaj].
  specialize (imaj (max n (max i j))
                   (le_trans _ _ _ (Nat.le_max_l i j) (Nat.le_max_r _ _))).
  specialize (H5 (max n (max i j))).
  destruct (H1 (max n (max i j))) as [s a0], a0, H6, H7.
  (* Locate x in an open interval ]s k, s (k+1)[ *)
  destruct (FindInterval s x O (qn (max n (max i j))) H7 H5) as [k kmaj].
  split. rewrite H3. exact imaj. rewrite H6.
  apply (CRlt_le_trans _ _ _ jmaj). apply CR_of_Q_le.
  unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
  apply Nat2Z.inj_le. apply (le_trans _ (2+j)).
  apply le_S, le_S, le_refl. apply le_n_S, le_n_S.
  exact (le_trans _ _ _ (Nat.le_max_r i _) (Nat.le_max_r _ _)).
  apply le_refl.
  destruct (IntervalOpenEta (s k) (s (S k)) x kmaj) as [eta etamaj].
  destruct etamaj.
  assert (0 < x - eta < x).
  { split. 2: exact (snd p). apply (CRle_lt_trans _ (s k)).
    2: exact (fst p). apply (CRle_trans _ (s O)).
    rewrite H3. apply CRlt_asym, anPos.
    apply growing_transit. exact H7. apply le_0_n. }
  exists (Build_IntervalExtension _ _ _ _ H9 (fst p0)). simpl.
  apply (CRle_lt_trans _ (CR_of_Q _ (1 # Pos.of_nat n))).
  specialize (H8 k (x - eta) x x (x + eta) H9).
  apply (CRle_trans _ (CR_of_Q (RealT (ElemFunc IS))
                               (1 # Pos.of_nat (max n (max i j))))).
  apply H8. 2: exact (CRle_refl x).
  exact (fst p). exact (snd p0). apply CR_of_Q_le. unfold Qle, Qnum, Qden.
  do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos.
  rewrite Nat2Pos.inj_max. apply Pos.le_max_l.
  apply (CRmult_lt_compat_l eps) in nmaj. rewrite CRinv_r in nmaj.
  destruct n. exfalso. rewrite CR_of_Q_zero, CRmult_0_r in nmaj.
  contradict nmaj. apply CRlt_asym, CRzero_lt_one.
  apply (CRmult_lt_reg_r (CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (S n) # 1))).
  apply CR_of_Q_pos. reflexivity. rewrite <- CR_of_Q_mult.
  setoid_replace ((1 # Pos.of_nat (S n)) * (Z.of_nat (S n) # 1))%Q with 1%Q.
  rewrite CR_of_Q_one. exact nmaj.
  unfold Qmult, Qeq, Qnum, Qden.
  rewrite Z.mul_1_l, Z.mul_1_l, Z.mul_1_r, Pos.mul_1_r.
  simpl (Z.of_nat (S n)). apply f_equal. rewrite Pos.of_nat_succ.
  reflexivity. exact H4.
Qed.

Lemma InverseImageIntegrableAE
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
    { s : nat -> CRcarrier (RealT (ElemFunc IS))
      & forall t (tPos : 0 < t),
      (forall n:nat, CRapart _ t (s n))
      -> { limInt : IntegrableSet (fun x => exists xD:Domain f x, t <= partialApply f x xD)
                   & CR_cv _ (fun n:nat => Integral (StepApproxIntegrable
                                                  f _ t (StepApproxBetween t tPos n) fInt))
                           (MeasureSet limInt) } }.
Proof.
  intros.
  destruct (FindJumpPointsCountable f fInt).
  exists x. intros.
  apply (InverseImageIntegrableGivenLimit f fInt t tPos).
  apply StepApproxBoundCv. apply (s t tPos H).
Qed.

(* In any integration space, construct a subset of positive measure. *)
Lemma IoneValSplit
  : forall {IS : IntegrationSpace},
    { nk : prod nat nat
           & I IS (XminConst (Xabs (Ione IS)) (CR_of_Q _ (1# Pos.of_nat (S (snd nk)))))
               (LminConstStable (CR_of_Q _ (1# Pos.of_nat (S (snd nk))))
                                (Xabs (Ione IS))
                                (invSuccRealPositive (snd nk))
                                (LabsStable (ElemFunc IS) (Ione IS) (IoneL IS)))
             < I IS (XminConst (Xabs (Ione IS)) (INR (2 + (fst nk))))
                 (LminIntStable (2 + (fst nk)) (Xabs (Ione IS))
                                (LabsStable _ _ (IoneL IS))) }.
Proof.
  intro IS.
  assert (0 < I IS (Xabs (Ione IS)) (LabsStable _ _ (IoneL IS))).
  { apply (CRlt_le_trans _ 1). apply CRzero_lt_one.
    rewrite <- IoneInt. apply INonDecreasing. intros.
    simpl. rewrite (DomainProp _ x xF y). apply CRle_abs. }
  pose proof (Ilimit IS (Ione IS) (IoneL IS)) as [_ lowInt].
  pose proof (CR_cv_open_above _ _ _ lowInt H) as [k kmaj].
  specialize (kmaj k (le_refl k)).
  pose proof (Ilimit IS (Xabs (Ione IS)) (LabsStable _ _ (IoneL IS)))
    as [highInt _].
  pose proof (CR_cv_open_below _ _ _ highInt kmaj) as [n nmaj].
  exists (pair n k). apply nmaj. unfold fst. apply le_S, le_S, le_refl.
Qed.

Record PositiveMeasureSubset {IS : IntegrationSpace} :=
  { pms_subset : X (ElemFunc IS) -> Prop;
    pms_int : IntegrableSet pms_subset;
    pms_pos : 0 < MeasureSet pms_int;
  }.

Lemma StepApproxMax
  : forall {R : ConstructiveReals}
      (c s2 t2 : CRcarrier R) (ltst2 : s2 < t2),
  s2 <= t2
  -> CRinv R (t2 - s2) (inr (CRlt_minus s2 t2 ltst2)) *
    (CRmin c t2 + - CRmin c s2) <= 1.
Proof.
  intros. apply (CRmult_le_reg_l (t2-s2)).
  apply CRlt_minus, ltst2.
  rewrite <- CRmult_assoc, CRinv_r, CRmult_1_l, CRmult_1_r.
  apply (CRle_trans _ _ _ (CRle_abs _)).
  rewrite CRmin_sym, (CRmin_sym c s2).
  apply (CRle_trans _ _ _ (CRmin_contract _ _ _)).
  rewrite CRabs_right. apply CRle_refl.
  apply CRlt_asym, CRlt_minus, ltst2.
Qed.

Lemma PositiveMeasureSubsetExists
  : forall (IS : IntegrationSpace), @PositiveMeasureSubset IS.
Proof.
  intro IS. destruct (@IoneValSplit IS) as [[n k] H].
  unfold fst, snd in H.
  assert (1 # Pos.of_nat (S k) < Z.of_nat (2 + n) # 1)%Q.
  { unfold Qlt, Qnum, Qden. rewrite Z.mul_1_l.
    apply (Z.lt_le_trans _ (Z.of_nat (2+n)*1)).
    rewrite Z.mul_1_r. replace 1%Z with (Z.of_nat 1).
    apply Nat2Z.inj_lt. apply le_n_S, le_n_S, le_0_n. reflexivity.
    apply Z.mul_le_mono_nonneg_l. discriminate.
    apply Pos2Z.pos_le_pos. apply Pos.le_1_l. }
  pose proof (InverseImageIntegrableAE
                (Xabs (Ione IS)) (IntegrableL _ (LabsStable _ _ (IoneL IS))))
    as [s sint].
  assert (0 < CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S k)) < INR (2 + n)).
  { split. apply CR_of_Q_pos. reflexivity. apply CR_of_Q_lt. exact H0. }
  destruct (CRuncountable s 0 (CR_of_Q _ (1 # Pos.of_nat (S k))) (fst H1))
    as [t tap].
  destruct tap. specialize (sint t (fst p) c). destruct sint.
  assert (0 < MeasureSet x).
  { apply (CRlt_le_trans
             _ (Integral (StepApproxIntegrable
                            (Xabs (Ione IS))
                            (CR_of_Q _ (1 # Pos.of_nat (S k))) (INR (2 + n)) H1
                            (IntegrableL _ (LabsStable _ _ (IoneL IS)))))).
    unfold StepApproxIntegrable.
    rewrite (IntegralScale (Xminus (XminConst (Xabs (Ione IS)) (INR (2 + n)))
          (XminConst (Xabs (Ione IS))
                     (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S k)))))
                           _
                          (CRinv (RealT (ElemFunc IS))
          (INR (2 + n) - CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S k)))
          (inr
             (CRlt_minus (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S k)))
                (INR (2 + n)) (snd H1)))) ).
    apply CRmult_lt_0_compat. rewrite IntegralMinus.
    apply CRlt_minus.
    apply (CRle_lt_trans _ (Integral (IntegrableL _ (LminConstStable (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S k)))
           (Xabs (Ione IS)) (invSuccRealPositive k)
           (LabsStable (ElemFunc IS) (Ione IS) (IoneL IS)))))).
    apply IntegralNonDecreasing. intros y ydf ydg.
    rewrite (DomainProp _ y ydf ydg). apply CRle_refl.
    rewrite IntegralLstable.
    apply (CRlt_le_trans _ _ _ H).
    apply (CRle_trans _ (Integral (IntegrableL _ (LminIntStable (2 + n) (Xabs (Ione IS))
                                                                (LabsStable (ElemFunc IS) (Ione IS) (IoneL IS)))))).
    rewrite IntegralLstable. apply CRle_refl.
    apply IntegralNonDecreasing. intros y ydf ydg.
    rewrite (DomainProp _ y ydf ydg). apply CRle_refl.
    apply CRinv_0_lt_compat, CRlt_minus, CR_of_Q_lt. exact H0.
    apply IntegralNonDecreasing. intros y ydf ydg.
    simpl ( partialApply (CharacFunc
       (fun x0 : X (ElemFunc IS) =>
        exists xD : Domain (Xabs (Ione IS)) x0,
          t <= partialApply (Xabs (Ione IS)) x0 xD)) y ydg).
    destruct ydg.
    - unfold StepApprox. rewrite applyXscale.
      destruct ydf.
      rewrite (applyXminus _ (XminConst (Xabs (Ione IS))
          (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S k))))).
      do 2 rewrite applyXminConst. rewrite (DomainProp (Xabs (Ione IS)) y d0 d).
      apply StepApproxMax. apply CRlt_asym, CR_of_Q_lt. exact H0.
    - destruct (CRltLinear (RealT (ElemFunc IS))).
      destruct ydf.
      destruct (s0 t (partialApply (Xabs (Ione IS)) y d0)
                   (CR_of_Q _ (1 # Pos.of_nat (S k))) (snd p)).
      exfalso. apply n0. exists d0. apply CRlt_asym, c1.
      unfold StepApprox. rewrite applyXscale.
      apply (CRmult_le_reg_l (INR (2 + n) - CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S k)))).
      apply CRlt_minus, CR_of_Q_lt. exact H0.
      rewrite <- CRmult_assoc, CRinv_r, CRmult_0_r, CRmult_1_l.
      rewrite (applyXminus _ (XminConst (Xabs (Ione IS))
          (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S k))))).
      do 2 rewrite applyXminConst. rewrite (DomainProp (Xabs (Ione IS)) y d d0).
      unfold CRminus.
      rewrite CRmin_left, CRmin_left, CRplus_opp_r. apply CRle_refl.
      apply CRlt_asym, c1. apply CRlt_asym.
      apply (CRlt_trans _ _ _ c1). apply CR_of_Q_lt. exact H0. }
  exact (Build_PositiveMeasureSubset IS _ x H2).
Qed.
