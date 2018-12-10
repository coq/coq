(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Cast of constructive reals inside an integration space.
    Because two instances of constructive reals are isomorphic,
    so are their integrations spaces. *)

Require Import QArith_base.
Require Import List.
Require Import ConstructiveReals.
Require Import ConstructiveRealsMorphisms.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructivePartialFunctions.
Require Import CMTbase.
Require Import CMTIntegrableFunctions.
Require Import CMTIntegrableSets.
Require Import CMTFullSets.

Local Open Scope ConstructiveReals.

Definition CRcast {R1 R2 : ConstructiveReals} : CRcarrier R1 -> CRcarrier R2
  := CRmorph (@SlowConstructiveRealsMorphism R1 R2).

Definition PartialFunctionCast {R1 R2 : ConstructiveReals} {X : Set}
           (f : @PartialFunction R1 X) : @PartialFunction R2 X.
Proof.
  apply (Build_PartialFunctionXY
           X (CRcarrier R2) (CReq R2) (Domain f)
           (fun x xD => CRcast (partialApply f x xD))).
  intros. apply CRmorph_proper. apply DomainProp.
Defined.

Definition FunctionRieszSpaceCast {R : ConstructiveReals}
  : FunctionRieszSpace -> FunctionRieszSpace.
Proof.
  intro el.
  apply (Build_FunctionRieszSpace
           (X el) R (fun f => L el (@PartialFunctionCast R _ (X el) f))).
  - intros. destruct el.
    apply (Lext (PartialFunctionCast f)). 2: exact X.
    destruct H, p.
    split. split.
    intros x xD. exact (d x xD).
    intros x xD. exact (d0 x xD).
    intros. apply CRmorph_proper, c.
  - intros. destruct el.
    apply (Lext (Xplus (PartialFunctionCast f) (PartialFunctionCast g))).
    split. split.
    intros x xD. exact xD.
    intros x xD. exact xD.
    intros. destruct xD, xG. simpl.
    unfold CRcast. rewrite <- CRmorph_plus. apply CRmorph_proper.
    apply CRplus_morph; apply DomainProp.
    apply LplusStable; assumption.
  - intros. destruct el.
    apply (Lext (Xabs (PartialFunctionCast f))).
    split. split.
    intros x xD. exact xD.
    intros x xD. exact xD.
    intros. simpl.
    unfold CRcast. rewrite CRmorph_abs. apply CRmorph_proper.
    apply CRabs_morph, DomainProp. apply LabsStable, X.
  - intros. destruct el.
    apply (Lext (XminConst (PartialFunctionCast f) 1)).
    split. split.
    intros x xD. exact xD.
    intros x xD. exact xD.
    intros. simpl. unfold CRcast.
    rewrite CRmorph_min. apply CRmin_morph.
    apply CRmorph_proper, DomainProp.
    symmetry. apply CRmorph_one. apply LminOneStable, X.
  - intros. destruct el.
    apply (Lext (Xscale (CRcast a) (PartialFunctionCast f))).
    split. split.
    intros x xD. exact xD.
    intros x xD. exact xD.
    intros. simpl. unfold CRcast. rewrite <- CRmorph_mult.
    apply CRmorph_proper. apply CRmult_morph. reflexivity. apply DomainProp.
    apply LscaleStable, X.
Defined.


Lemma IadditiveCast
  : forall (IS : IntegrationSpace) {R : ConstructiveReals}
      (f g : PartialFunction (X (FunctionRieszSpaceCast (ElemFunc IS))))
      (fL : L (FunctionRieszSpaceCast (ElemFunc IS)) f)
      (gL : L (FunctionRieszSpaceCast (ElemFunc IS)) g),
    CRcast (I IS (PartialFunctionCast (Xplus f g))
               (LplusStable (@FunctionRieszSpaceCast R (ElemFunc IS)) f g fL gL)) ==
    CRcast (I IS (PartialFunctionCast f) fL) +
    @CRcast (RealT (ElemFunc IS)) R (I IS (PartialFunctionCast g) gL).
Proof.
  intros. unfold CRcast.
  rewrite <- CRmorph_plus. apply CRmorph_proper.
  rewrite <- (Iadditive IS). apply IExtensional.
  intros. simpl. destruct xF, y.
  unfold CRcast. rewrite <- CRmorph_plus. apply CRmorph_proper.
  apply CRplus_morph; apply DomainProp.
Qed.

Lemma IhomogeneousCast
  : forall (IS : IntegrationSpace) {R : ConstructiveReals}
      (a : CRcarrier (RealT (FunctionRieszSpaceCast (ElemFunc IS))))
    (f : PartialFunction (X (FunctionRieszSpaceCast (ElemFunc IS))))
    (fL : L (FunctionRieszSpaceCast (ElemFunc IS)) f),
    CRcast (I IS (PartialFunctionCast (Xscale a f))
               (LscaleStable (@FunctionRieszSpaceCast R (ElemFunc IS)) a f fL))
    == a * CRcast (I IS (PartialFunctionCast f) fL).
Proof.
  intros. unfold CRcast.
  rewrite (CRmorph_proper
             _
             (I IS (PartialFunctionCast (Xscale a f))
                (LscaleStable (FunctionRieszSpaceCast (ElemFunc IS)) a f fL))
             (CRcast a * I IS (PartialFunctionCast f) fL)).
  rewrite CRmorph_mult. apply CRmult_morph.
  unfold CRcast.
  simpl in a.
  transitivity (CRmorph (CRmorph_compose
                           (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast (ElemFunc IS)))
                                                          (RealT (ElemFunc IS)))
                           (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                        ) a).
  unfold CRmorph_compose, CRmorph. reflexivity.
  apply Endomorph_id.
  reflexivity. rewrite <- (Ihomogeneous IS).
  apply IExtensional. intros. simpl.
  unfold CRcast. rewrite <- CRmorph_mult. apply CRmorph_proper.
  apply CRmult_morph. reflexivity. apply DomainProp.
Qed.

Lemma LElemFuncCastReverse : forall (E : FunctionRieszSpace) {R : ConstructiveReals}
                               (f : PartialFunction (X E)),
    L E f
    -> L (@FunctionRieszSpaceCast R E) (PartialFunctionCast f).
Proof.
  intros E R f fL. simpl.
  apply (Lext _ f). split. split.
  intros x xD. exact xD.
  intros x xD. exact xD.
  intros. simpl. unfold CRcast.
  transitivity (CRmorph (CRmorph_compose
                           (@SlowConstructiveRealsMorphism (RealT E) R)
                           (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast E))
                                                          (RealT E))
                        ) (partialApply f x xG)).
  rewrite Endomorph_id. apply DomainProp. reflexivity.
  apply fL.
Qed.

Lemma IcontinuousCast : forall (IS : IntegrationSpace) {R : ConstructiveReals},
  ElemIntegralContinuous
    (fun (f : PartialFunction (X (FunctionRieszSpaceCast (ElemFunc IS))))
         (fL : L (@FunctionRieszSpaceCast R (ElemFunc IS)) f) =>
       CRcast (I IS (PartialFunctionCast f) fL)).
Proof.
  intros IS R f fn fL fnL fnPos [l [lcv lmaj]].
  destruct (Icontinuous
              IS (PartialFunctionCast f) (fun n => PartialFunctionCast (fn n))
              fL fnL).
  - intros n x xdf. simpl. unfold CRcast.
    rewrite <- (CRmorph_zero (@SlowConstructiveRealsMorphism R (RealT (ElemFunc IS)))).
    apply CRmorph_le, fnPos.
  - exists (CRcast l). split.
    apply (series_cv_eq
             (fun n => (CRmorph (CRmorph_compose
                                (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                                (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast (ElemFunc IS)))
                                                               (RealT (ElemFunc IS)))
                             ) (I IS (PartialFunctionCast (fn n)) (fnL n))))).
    intro n. apply Endomorph_id.
    unfold CRmorph_compose, CRmorph. apply CRmorph_series_cv, lcv.
    rewrite <- (Endomorph_id
                 (CRmorph_compose
                    (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                    (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast (ElemFunc IS)))
                                                    (RealT (ElemFunc IS)))
                 )
                 (I IS (PartialFunctionCast f) fL)).
    unfold CRcast. unfold CRmorph_compose, CRmorph.
    apply CRmorph_increasing. exact lmaj.
  - destruct x. simpl in s.
    exists (Build_CommonPointFunSeq _ _ f fn cpx cpxF cpxFn).
    simpl. destruct s. exists (CRcast x). split.
    apply (series_cv_eq
             (fun n => (CRmorph (CRmorph_compose
                                (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast (ElemFunc IS)))
                                                               (RealT (ElemFunc IS)))
                                (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                             ) (partialApply (fn n) cpx (cpxFn n))))).
    intro n. apply Endomorph_id.
    unfold CRmorph_compose, CRmorph. apply CRmorph_series_cv, p.
    rewrite <- (Endomorph_id
                 (CRmorph_compose
                    (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast (ElemFunc IS)))
                                                   (RealT (ElemFunc IS)))
                    (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                 )
                 (partialApply f cpx cpxF)).
    unfold CRcast. unfold CRmorph_compose, CRmorph.
    apply CRmorph_increasing. apply p.
Qed.

Definition IntegrationSpaceCast {R : ConstructiveReals}
  : IntegrationSpace -> IntegrationSpace.
Proof.
  intro IS.
  apply (Build_IntegrationSpace
           (@FunctionRieszSpaceCast R (ElemFunc IS))
           (fun f fL => CRcast (I IS (PartialFunctionCast f) fL))
           (IadditiveCast IS) (IhomogeneousCast IS)
           (@PartialFunctionCast _ R _ (Ione IS))
           (LElemFuncCastReverse _ _ (IoneL IS))).
  - unfold CRcast.
    rewrite (CRmorph_proper _ (I IS (PartialFunctionCast (PartialFunctionCast (Ione IS))) (LElemFuncCastReverse _ _ (IoneL IS))) 1).
    apply CRmorph_one.
    rewrite <- IoneInt. apply IExtensional. intros.
    simpl.
    transitivity (CRmorph (CRmorph_compose
                             (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                             (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast (ElemFunc IS)))
                                                            (RealT (ElemFunc IS)))
                          ) (partialApply (Ione IS) x xF)).
    unfold CRmorph_compose, CRmorph; reflexivity.
    rewrite Endomorph_id. apply DomainProp.
  - exact (IcontinuousCast IS).
  - intros.
    pose proof (Ilimit IS (PartialFunctionCast f) fL) as [H H0].
    split. clear H0. apply CRmorph_cv.
    simpl. simpl in H. simpl in fL, f.
    apply (CR_cv_eq _ (fun n : nat =>
         I IS (XminConst (PartialFunctionCast f) (INR n))
           (LminIntStable n (PartialFunctionCast f) fL))).
    2: exact H.
    intro n. apply IExtensional. intros.
    simpl. unfold CRcast. rewrite CRmorph_min. apply CRmin_morph.
    apply CRmorph_proper, DomainProp. rewrite CRmorph_INR. reflexivity.
    apply (CR_cv_proper _ (@CRcast (RealT (ElemFunc IS)) R 0) 0).
    2: apply CRmorph_zero.
    apply CRmorph_cv.
    apply (CR_cv_eq _ (fun n : nat =>
          I IS
            (XminConst (Xabs (PartialFunctionCast f))
               (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S n))))
            (LminConstStable (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S n)))
               (Xabs (PartialFunctionCast f)) (invSuccRealPositive n)
               (LabsStable (ElemFunc IS) (PartialFunctionCast f) fL)))).
    2: exact H0.
    intro n. apply IExtensional. intros. simpl.
    unfold CRcast. rewrite CRmorph_min. apply CRmin_morph.
    rewrite CRmorph_abs. apply CRmorph_proper, CRabs_morph, DomainProp.
    symmetry. apply CRmorph_rat.
Defined.

Definition IntegrableFunctionCast {IS : IntegrationSpace} {R : ConstructiveReals}
           (f : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> @IntegrableFunction (@IntegrationSpaceCast R IS)
                          (@PartialFunctionCast (RealT (ElemFunc IS)) R _ f).
Proof.
  intros fInt. destruct fInt, x.
  assert (series_cv
    (fun k : nat =>
       @Iabs (@IntegrationSpaceCast R IS)
             (@PartialFunctionCast _ R _ (IntFn k))
             (LElemFuncCastReverse (ElemFunc IS) (IntFn k) (IntFnL k)))
    (CRcast IntAbsSum)).
  { apply CRmorph_series_cv.
    apply (series_cv_eq (fun k : nat => Iabs (IntFn k) (IntFnL k))).
    2: exact IntAbsSumCv. intro n. apply IExtensional.
    intros. simpl. unfold CRcast. rewrite <- CRmorph_abs.
    apply CRabs_morph.
    transitivity (CRmorph
                    (CRmorph_compose
                       (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                       (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast (ElemFunc IS)))
                                                      (RealT (ElemFunc IS))))
                    (partialApply (IntFn n) x y)).
    rewrite Endomorph_id. apply DomainProp. reflexivity. }
  exists (Build_IntegralRepresentation
       (@IntegrationSpaceCast R IS)
       (fun n => @PartialFunctionCast (RealT (ElemFunc IS)) R _ (IntFn n))
       (fun n => LElemFuncCastReverse _ _ (IntFnL n))
       (CRcast IntAbsSum) H).
  simpl. simpl in p.
  assert (@DomainInclusion R _
                           (XinfiniteSumAbs (fun n : nat => PartialFunctionCast (IntFn n)))
                           (PartialFunctionCast (XinfiniteSumAbs IntFn)))
    as incCast.
  { intros y ydf. simpl. simpl in ydf.
    destruct ydf. exists x. unfold CRcast in c.
    apply (CRmorph_cauchy_reverse
             (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)).
    apply (CR_cauchy_eq (CRsum
           (fun n : nat =>
            CRabs R
              (CRmorph (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                       (partialApply (IntFn n) y (x n)))))).
    2: exact c. intro n.
    rewrite CRmorph_sum. apply CRsum_eq.
    intros. rewrite CRmorph_abs. reflexivity. }
  split. simpl.
  - intros y ydf. simpl. specialize (incCast y). destruct p.
    apply d. apply incCast. exact ydf.
  - intros. destruct p.
    specialize (c x (incCast x xD) xG).
    simpl. apply applyInfiniteSumAbs in c.
    destruct xD. symmetry. apply series_cv_abs_eq.
    apply CRmorph_series_cv.
    apply (series_cv_eq (fun n : nat =>
         partialApply (IntFn n) x
           (domainInfiniteSumAbsIncReverse IntFn x
              (incCast x
                 (existT _ x0 c0)) n))).
    2: exact c. intro n. apply DomainProp.
Defined.

Lemma IntegralFunctionCast
  : forall {IS : IntegrationSpace} {R : ConstructiveReals}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
    Integral (@IntegrableFunctionCast IS R f fInt)
    == CRcast (Integral fInt).
Proof.
  intros. unfold Integral.
  apply (series_cv_unique _ _ _ (IntegralCv
                         (let (i, _) := IntegrableFunctionCast f fInt in i))).
  apply CRmorph_series_cv.
  apply (series_cv_eq (fun n : nat =>
         I IS (IntFn (let (i, _) := fInt in i) n) (IntFnL (let (i, _) := fInt in i) n))).
  2: exact (IntegralCv (let (i, _) := fInt in i)). intro n.
  apply IExtensional. intros. destruct fInt, x0.
  unfold IntegrableFunctionCast, CMTIntegrableFunctions.IntFn.
  simpl. unfold CRcast.
  transitivity (CRmorph
                  (CRmorph_compose
                     (@SlowConstructiveRealsMorphism (RealT (ElemFunc IS)) R)
                     (@SlowConstructiveRealsMorphism (RealT (FunctionRieszSpaceCast (ElemFunc IS)))
                                                    (RealT (ElemFunc IS))))
                  (partialApply (IntFn n) x y)).
  rewrite Endomorph_id. apply DomainProp. reflexivity.
Qed.
