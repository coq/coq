(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import QArith.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveLimits.
Require Import ConstructivePartialFunctions.
Require Import CMTbase.
Require Import CMTIntegrableFunctions.
Require Import CMTFullSets.
Require Import CMTIntegrableSets.
Require Import CMTprofile.

Local Open Scope ConstructiveReals.


(* A function f is measurable when it is integrable on any
   integrable rectangle A * [-k,k]. *)
Definition MeasurableFunction {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS))) : Type
  := forall (A : (X (ElemFunc IS)) -> Prop) (k : positive),
    IntegrableSet A
    -> IntegrableFunction (XmaxConst (XminConst (Xmult (CharacFunc A) f)
                                               (CR_of_Q _ (Z.pos k # 1)))
                                    (CR_of_Q _ (Z.neg k # 1))).

Lemma MeasurableFunctionExtensional
  : forall {IS : IntegrationSpace}
           (f g : PartialFunction (X (ElemFunc IS))),
    PartialRestriction f g
    -> MeasurableFunction f
    -> MeasurableFunction g.
Proof.
  intros IS f g [d c] fMes A k Aint.
  apply (IntegrableFunctionExtensional
           (XmaxConst (XminConst (Xmult (CharacFunc A) f)
                                 (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
                      (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))).
  2: exact (fMes A k Aint).
  split.
  - intros x xdf. simpl in xdf. destruct xdf.
    split. exact s. exact (d x d0).
  - intros. simpl. destruct xD, xG.
    rewrite (c x d1 (d x d1)), (DomainProp g x (d x d1) d3).
    destruct d0. destruct d2. reflexivity. contradiction.
    destruct d2. contradiction. reflexivity.
Qed.

Lemma MeasurableFunctionFull
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS))),
    MeasurableFunction f
    -> almost_everywhere (Domain f).
Proof.
  intros IS f fMes.
  destruct (@PositiveMeasureSubsetExists IS) as [A Aint Apos].
  specialize (fMes A 1%positive Aint).
  exists (XmaxConst (XminConst (Xmult (CharacFunc A) f) (CR_of_Q (RealT (ElemFunc IS)) 1))
              (CR_of_Q (RealT (ElemFunc IS)) (-1))).
  split. exact fMes.
  intros x xD. apply xD.
Qed.

Lemma MeasurableConst
  : forall {IS : IntegrationSpace}
      (a : CRcarrier (RealT (ElemFunc IS))),
    MeasurableFunction (Xconst (X (ElemFunc IS)) a).
Proof.
  intros IS a A k Aint. apply IntegrableMaxConst.
  apply IntegrableMinConst.
  apply (IntegrableFunctionExtensional (Xscale a (CharacFunc A))).
  - split. intros x xdf.
    split. exact xdf. simpl. trivial. intros. simpl.
    destruct xG. destruct xD. destruct d. apply CRmult_comm.
    contradiction. destruct d. contradiction. apply CRmult_comm.
  - apply IntegrableScale, Aint.
  - rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
  - rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
Qed.

Lemma IntegrableMeasurableSet
  : forall {IS : IntegrationSpace}
      (A : X (ElemFunc IS) -> Prop),
    IntegrableSet A -> MeasurableSet A.
Proof.
  intros IS A Aint B Bint.
  exact (IntegrableSetIntersect _ _ Aint Bint).
Qed.

(* In finite integration spaces, like probability spaces, measurable is
   equivalent to integrable. *)
Lemma MeasurableIntegrableSubset
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop),
    IntegrableSet B
    -> MeasurableSet A
    -> (forall x : X (ElemFunc IS), A x -> B x)
    -> IntegrableSet A.
Proof.
  intros IS A B Bint Ames incl.
  specialize (Ames B Bint).
  apply (IntegrableSetExtensional
           (fun x : X (ElemFunc IS) => A x /\ B x)).
  2: exact Ames.
  split. intros. apply H. intros. split. exact H. exact (incl x H).
Qed.

Lemma TruncOpp : forall {R : ConstructiveReals} (x : CRcarrier R) (k : positive),
    - CRmax (CRmin x (CR_of_Q _ (Z.pos k # 1)))
            (CR_of_Q _ (Z.neg k # 1))
    == CRmax (CRmin (-x) (CR_of_Q _ (Z.pos k # 1)))
             (CR_of_Q _ (Z.neg k # 1)).
Proof.
  intros. destruct (CRltLinear R).
  setoid_replace (-x) with (-CRone R * x).
  destruct (s (CR_of_Q R (Z.neg k # 1)) x 0).
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
  rewrite CRmax_left, (CRmin_left (- (1) * x)).
  - setoid_replace (CR_of_Q R (Z.neg k # 1))
      with (-CRone R * CR_of_Q R (Z.pos k # 1)).
    rewrite CRmax_min_mult_neg. rewrite <- CRopp_mult_distr_l.
    rewrite CRmult_1_l. reflexivity.
    apply (CRplus_le_reg_l 1). rewrite CRplus_opp_r, CRplus_0_r.
    apply CRlt_asym, CRzero_lt_one.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l, <- CR_of_Q_opp.
    apply CR_of_Q_morph. reflexivity.
  - rewrite <- CRopp_mult_distr_l, CRmult_1_l.
    rewrite <- (CRopp_involutive (CR_of_Q R (Z.pos k # 1))).
    apply CRopp_ge_le_contravar. rewrite <- CR_of_Q_opp.
    apply (CRle_trans _ (CR_of_Q R (Z.neg k # 1))).
    apply CR_of_Q_le. apply Qle_refl. apply CRlt_asym, c.
  - apply CRmin_glb. apply CRlt_asym, c. apply CR_of_Q_le. discriminate.
  - rewrite CRmin_left, (CRmax_left (CRmin (- (1) * x) (CR_of_Q R (Z.pos k # 1)))).
    setoid_replace (CR_of_Q R (Z.pos k # 1))
      with (-CRone R * CR_of_Q R (Z.neg k # 1)).
    rewrite CRmin_max_mult_neg, <- CRopp_mult_distr_l, CRmult_1_l. reflexivity.
    apply (CRplus_le_reg_l 1). rewrite CRplus_opp_r, CRplus_0_r.
    apply CRlt_asym, CRzero_lt_one.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l, <- CR_of_Q_opp.
    apply CR_of_Q_morph. reflexivity.
    apply CRmin_glb. apply (CRle_trans _ 0).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l, <- CRopp_0.
    apply CRopp_ge_le_contravar, CRlt_asym, c.
    apply CR_of_Q_le. discriminate.
    apply (CRle_trans _ 0). apply CRlt_asym, c.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  - rewrite <- CRopp_mult_distr_l, CRmult_1_l. reflexivity.
Qed.

Lemma TruncPosNeg : forall {R : ConstructiveReals} (y : CRcarrier R) (k : positive),
   CRmax (CRmin (CRmax 0 y) (CR_of_Q R (Z.pos k # 1)))
    (CR_of_Q R (Z.neg k # 1)) +
  CRmax (CRmin (CRmin 0 y) (CR_of_Q R (Z.pos k # 1)))
    (CR_of_Q R (Z.neg k # 1)) ==
  CRmax (CRmin y (CR_of_Q R (Z.pos k # 1)))
    (CR_of_Q R (Z.neg k # 1)).
Proof.
  intros.
  rewrite (CRmax_left (CRmin (CRmax 0 y) (CR_of_Q R (Z.pos k # 1)))).
  rewrite (CRmin_left (CRmin 0 y)).
  - destruct (CRltLinear R).
    destruct (s (CR_of_Q R (Z.neg k # 1)) y 0).
    + rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    + rewrite (CRmax_left (CRmin y (CR_of_Q R (Z.pos k # 1)))).
      rewrite (CRmax_left (CRmin 0 y)).
      destruct (s 0 y (CR_of_Q R (Z.pos k # 1))).
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      rewrite CRmax_right, (CRmin_left 0 y). rewrite CRplus_0_r. reflexivity.
      apply CRlt_asym, c0. apply CRlt_asym, c0.
      rewrite (CRmin_left y), CRmin_left.
      unfold CRmax, CRmin.
      rewrite CRplus_0_l, <- CRmult_plus_distr_r.
      unfold CRminus. rewrite CRplus_assoc, <- (CRplus_comm (- CRabs R (y + - 0))).
      rewrite <- (CRplus_assoc (CRabs R (y + - 0))), CRplus_opp_r, CRplus_0_l.
      apply (CRmult_eq_reg_r (CR_of_Q R 2)).
      left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
      rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_1_r, CRmult_plus_distr_l.
      rewrite CRmult_1_r. reflexivity.
      apply CRmax_lub.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRlt_asym, c0. apply CRlt_asym, c0.
      apply CRmin_glb.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRlt_asym, c. apply CRmin_glb.
      apply CRlt_asym, c. apply CR_of_Q_le. discriminate.
    + rewrite (CRmax_left 0 y). rewrite (CRmin_right 0 y).
      rewrite CRmin_left, CRplus_0_l. rewrite CRmin_left. reflexivity.
      apply (CRle_trans _ 0). apply CRlt_asym, c.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRlt_asym, c. apply CRlt_asym, c.
  - apply (CRle_trans _ 0). apply CRmin_l.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  - apply CRmin_glb. apply (CRle_trans _ 0).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRmax_l.
    apply CR_of_Q_le. discriminate.
Qed.

Definition MeasurablePosNegParts {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
  : MeasurableFunction (XposPart f)
    -> MeasurableFunction (XnegPart f)
    -> MeasurableFunction f.
Proof.
  intros fMes gMes A k Aint.
  apply (IntegrableFunctionExtensional
           (Xminus
              (XmaxConst (XminConst (Xmult (CharacFunc A) (XposPart f))
                                    (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
                         (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))
              (XmaxConst (XminConst (Xmult (CharacFunc A) (XnegPart f))
                                    (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
                         (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1))))).
  - split. intros x xdf. simpl. simpl in xdf. destruct xdf. split.
    apply p. apply p. intros. simpl.
    destruct xD, d, d0, d1, d2, xG.
    setoid_replace (if d5 then CRone (RealT (ElemFunc IS)) else 0)
      with (if d then CRone (RealT (ElemFunc IS)) else 0).
    setoid_replace (if d0 then CRone (RealT (ElemFunc IS)) else 0)
      with (if d then CRone (RealT (ElemFunc IS)) else 0).
    destruct d.
    + rewrite CRmult_1_l, CRmult_1_l, CRmult_1_l.
      rewrite (DomainProp f x d6 d1), (DomainProp f x d4 d1),
      (DomainProp f x d2 d1), (DomainProp f x d3 d1). clear d6 d4 d3 d2.
      generalize (partialApply f x d1). intro y.
      rewrite (CRmult_comm (CR_of_Q (RealT (ElemFunc IS)) (1 # 2))).
      rewrite <- CRposPartAbsMax.
      rewrite (CRmult_comm (CR_of_Q (RealT (ElemFunc IS)) (1 # 2))).
      do 2 rewrite <- CRopp_mult_distr_l. do 2 rewrite CRmult_1_l.
      rewrite TruncOpp, CRopp_mult_distr_l, CRopp_plus_distr.
      rewrite CRopp_involutive, <- (CRplus_comm y).
      pose proof (CRnegPartAbsMin y). unfold CRminus in H.
      rewrite <- H. clear H. apply TruncPosNeg.
    + rewrite CRmult_0_l, CRmult_0_l, CRmult_0_l.
      rewrite CRmin_left, CRmax_left, CRplus_0_l, CRmult_0_r. reflexivity.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    + destruct d0. destruct d. reflexivity. contradiction. destruct d.
      contradiction. reflexivity.
    + destruct d5. destruct d. reflexivity. contradiction. destruct d.
      contradiction. reflexivity.
  - apply IntegrableMinus. apply fMes, Aint. apply gMes, Aint.
Qed.

Lemma CR_cv_max : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (l a : CRcarrier R),
    CR_cv R un l
    -> CR_cv R (fun n : nat => CRmax (un n) a)
             (CRmax l a).
Proof.
  intros. intro p. specialize (H p) as [n H].
  exists n. intros.
  apply (CRle_trans _ _ _ (CRmax_contract _ _ a)).
  exact (H i H0).
Qed.

Lemma CR_cv_min : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (l a : CRcarrier R),
    CR_cv R un l
    -> CR_cv R (fun n : nat => CRmin (un n) a)
             (CRmin l a).
Proof.
  intros. intro p. specialize (H p) as [n H].
  exists n. intros.
  apply (CRle_trans _ _ _ (CRmin_contract _ _ a)).
  exact (H i H0).
Qed.

(* This proves that a Lebesgue-measurable function is Bishop-measurable,
   when we assume the classical theorem IncrSeqCvT.
   Because non-negative Lebesgue-measurable functions are non-decreasing
   limits of simple functions, which are Bishop-measurable. *)
Definition MeasurableMonotoneConvergenceClassical
           {IS : IntegrationSpace}
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
  : (forall n:nat, MeasurableFunction (fn n))
    -> (forall n:nat, partialFuncLe (fn n) (fn (S n)))
    -> IncrSeqCvT
         (* The sequence fn is assumed to converge everywhere,
            because the sequence fn is derived from a hypothetical
            Lebesgue-measurable function f, that we want to prove
            is Bishop-integrable.

            This hypothesis is necessary, to replace the convergence of
            integrals in the constructive monotone convergence theorem.
            For example, the sequence of constant measurable functions n
            converges nowhere, so we cannot conclude that the empty
            function is measurable. *)
    -> (forall x : X (ElemFunc IS),
           Domain (XpointwiseLimit fn) x)
    -> MeasurableFunction (XpointwiseLimit fn).
Proof.
  intros fnMes H cl cv A k Aint.
  assert (forall n:nat, partialFuncLe
    (XmaxConst (XminConst (Xmult (CharacFunc A) (fn n)) (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
       (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))
    (XmaxConst
       (XminConst (Xmult (CharacFunc A) (fn (S n))) (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
       (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))).
  { intros n x xdf xdg.
    simpl. destruct xdf, xdg. destruct d.
    destruct d1. 2: contradiction. rewrite CRmult_1_l, CRmult_1_l.
    apply CRmax_lub.
    apply (CRle_trans _ (CRmin (partialApply (fn (S n)) x d2) (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))).
    2: apply CRmax_l.
    apply CRmin_glb. 2: apply CRmin_r.
    apply (CRle_trans _ (partialApply (fn n) x d0)).
    apply CRmin_l. apply H. apply CRmax_r.
    destruct d1. contradiction. rewrite CRmult_0_l, CRmult_0_l. apply CRle_refl. }
  assert (forall n : nat,
        (fun n0 : nat => Integral (fnMes n0 A k Aint)) n <=
        (fun n0 : nat => Integral (fnMes n0 A k Aint)) (S n)).
  { intro n. apply IntegralNonDecreasing. apply H0. }
  assert (forall n : nat,
        (fun n0 : nat => Integral (fnMes n0 A k Aint)) n <=
        MeasureSet Aint * CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)).
  { intro n.
    apply (CRle_trans _ (Integral (IntegrableScale (CharacFunc A)
                                                     (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1))
                                                     Aint))).
    apply IntegralNonDecreasing. intros x xdf xdg.
    simpl. destruct xdf, xdg. destruct d. 2: contradiction.
    rewrite CRmult_1_l, CRmult_1_r. apply CRmax_lub.
    apply CRmin_r. apply CR_of_Q_le. discriminate.
    destruct d. contradiction. rewrite CRmult_0_l, CRmult_0_r.
    apply CRmax_lub. apply CRmin_l. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate.
    rewrite IntegralScale. apply CRle_refl. }
  destruct (CR_complete _ _ (cl _ (fun n => Integral (fnMes n A k Aint))
                 (MeasureSet Aint * CR_of_Q _ (Z.pos k # 1))
                 H1 H2)) as [l lcv].
  destruct (IntegralMonotoneConvergence
              IS (fun n => XmaxConst
       (XminConst (Xmult (CharacFunc A) (fn n))
                  (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1))) (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))
              (fun n => fnMes n A k Aint) l H0 lcv).
  apply (IntegrableFunctionExtensional
           (XpointwiseLimit
           (fun n : nat =>
            XmaxConst
              (XminConst (Xmult (CharacFunc A) (fn n)) (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
              (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1))))).
  2: exact x.
  split. intros y ydf. simpl. simpl in ydf. destruct ydf.
  split. exact (fst (x0 O)). exists (fun n => snd (x0 n)).
  specialize (cv y). destruct cv.
  apply (CR_cauchy_eq (fun n : nat => partialApply (fn n) y (x1 n))).
  2: exact c1. intro n. apply DomainProp.
  intros. apply applyPointwiseLimit. apply CR_cv_max.
  apply CR_cv_min. destruct xD, xG. destruct d.
  - setoid_replace (partialApply (Xmult (CharacFunc A) (XpointwiseLimit fn)) x0 (left a, d0))
      with (partialApply (XpointwiseLimit fn) x0 d0).
    2: simpl; rewrite CRmult_1_l; reflexivity.
    pose proof (applyPointwiseLimit fn x0 d0
                                    (partialApply (XpointwiseLimit fn) x0 d0)) as [H3 _].
    apply (CR_cv_eq _ (fun n : nat => partialApply (fn n) x0 (let (xn, _) := d0 in xn n))).
    intro n. simpl. destruct (x1 n), d. rewrite CRmult_1_l. apply DomainProp.
    contradiction. apply H3. reflexivity.
  - setoid_replace (partialApply (Xmult (CharacFunc A) (XpointwiseLimit fn)) x0 (right n, d0))
      with (CRzero (RealT (ElemFunc IS))).
    2: simpl; rewrite CRmult_0_l; reflexivity.
    apply (CR_cv_eq _ (fun _ => 0)). intros.
    simpl. destruct (x1 n0), d. contradiction. rewrite CRmult_0_l. reflexivity.
    intro p. exists O. intros. unfold CRminus.
    rewrite CRplus_opp_r, CRabs_right, <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate. apply CRle_refl.
Qed.

Definition SetApprox {IS : IntegrationSpace}
           (A B : (X (ElemFunc IS)) -> Prop)
           (eps : CRcarrier (RealT (ElemFunc IS))) : Type
  := { DiffInt : IntegrableSet (fun x => A x /\ ~B x)
                 & MeasureSet DiffInt < eps }.

Definition CvMeasure {IS : IntegrationSpace}
           (fn : nat -> @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS)))
           (f : @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS))) : Type
  := forall (A : (X (ElemFunc IS)) -> Prop)
       (eps : CRcarrier (RealT (ElemFunc IS))),
    0 < eps
    -> IntegrableSet A
    -> { N : nat  &  forall n:nat,
            le N n -> { B : (X (ElemFunc IS)) -> Prop
                       & prod (SetApprox A B eps)
                              (forall x xdf xdfn, B x -> CRabs _ (partialApply f x xdf - partialApply (fn n) x xdfn) < eps) } }.
