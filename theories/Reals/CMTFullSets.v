(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Following the invariance of the integral with respect to the representation,
   we now precisely define full sets, and prove that 2 functions equal on a
   full set have the same integral. *)

Require Import QArith.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveCauchyAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructiveDiagonal.
Require Import ConstructivePartialFunctions.

Require Import CMTbase.
Require Import CMTIntegrableFunctions.

Local Open Scope ConstructiveReals.


(* A full set of the integration space IS is a subset of X (ElemFunc IS)
   that contains the domain of an integrable function.

   In other words, a property P of an integration space IS
   holds almost everywhere when there is an integrable function h
   on which domain P holds. *)
Definition almost_everywhere {IS : IntegrationSpace}
           (P : X (ElemFunc IS) -> Type) : Type
  := { h : PartialFunction (X (ElemFunc IS))
           & prod (IntegrableFunction h)
                  (forall (x:X (ElemFunc IS)),
                      Domain h x -> P x) }.


(* We start with a lemma to help prove that sets are full : it suffices
   that they contain a countable intersection of domains of integrable functions.

   This is the complement of the usual property about Lebesgue null sets :
   a countable union of null sets is null. *)


Definition diagSeqL : forall (IS : IntegrationSpace)
                        (fnk : nat -> nat -> PartialFunction (X (ElemFunc IS)))
                        (fnkL : forall n k: nat, L (ElemFunc IS) (fnk n k))
                        (p : nat),
    L (ElemFunc IS) (diagSeq fnk p).
Proof.
  intros. unfold diagSeq. destruct (diagPlaneInv p). apply fnkL.
Defined.

Definition diagSeqDomain {R : ConstructiveReals} (X : Set)
           (fnk : nat -> nat -> @PartialFunction R X)
           (x : X)
           (xn : forall p:nat, Domain (diagSeq fnk p) x)
           (n k : nat)
  : Domain (fnk n k) x.
Proof.
  unfold diagSeq in xn. pose (xn (diagPlane n k)).
  rewrite diagPlaneInject in d. exact d.
Defined.

Definition countable_representation
           (IS : IntegrationSpace)
           (f : PartialFunction (X (ElemFunc IS)))
           (fInt : IntegrableFunction f)
           (n : nat)
  : { intRepres : IntegralRepresentation
                  & prod (DomainInclusion
                            (XinfiniteSumAbs (IntFn intRepres)) f)
                         (IntAbsSum intRepres <= CRpow (CR_of_Q _ (1#2)) n) }.
Proof.
  destruct fInt as [[fnk fnkL sumAbsIFnk] [injF restrict]].
  unfold IntFn in restrict, injF.
  assert (0 < (1 + sumAbsIFnk)) as denomPos.
  { apply (CRlt_le_trans 0 (1+0)). rewrite CRplus_0_r.
    apply CRzero_lt_one. apply CRplus_le_compat_l.
    apply (series_cv_nonneg (fun k : nat => Iabs (fnk k) (fnkL k))).
    intro n0. apply integralPositive. intros x xdf. rewrite applyXabs.
    apply CRabs_pos. assumption. }
  assert (series_cv
    (fun k : nat =>
     Iabs (Xscale (CRpow (CR_of_Q _ (1#2)) n * CRinv _ (1 + sumAbsIFnk) (inr denomPos)) (fnk k))
       (LscaleStable (ElemFunc IS) _ (fnk k) (fnkL k)))
    (sumAbsIFnk * (CRpow (CR_of_Q _ (1#2)) n * CRinv _ (1 + sumAbsIFnk) (inr denomPos)))) as H.
  { apply (series_cv_eq
             (fun b : nat =>
                Iabs (fnk b) (fnkL b) *
                (CRpow (CR_of_Q _ (1#2)) n * CRinv _ (1 + sumAbsIFnk) (inr denomPos)))).
    intro k. rewrite IabsHomogeneous. rewrite CRmult_comm.
    apply CRmult_morph. 2: reflexivity.
    rewrite CRabs_right. reflexivity. apply CRlt_asym.
    apply CRmult_lt_0_compat. apply pow_lt.
    simpl. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    apply CRinv_0_lt_compat. exact denomPos.
    apply series_cv_scale. assumption. }
  exists (Build_IntegralRepresentation
       IS
            (fun k : nat => Xscale (CRpow (CR_of_Q _ (1#2)) n * CRinv _ (1 + sumAbsIFnk) (inr denomPos)) (fnk k))
            (fun k => LscaleStable _ _ (fnk k) (fnkL k))
            (sumAbsIFnk * (CRpow (CR_of_Q _ (1#2)) n * CRinv _ (1 + sumAbsIFnk) (inr denomPos)))
            H).
  assert (CRapart _ (1 + sumAbsIFnk) 0) as denomNonZero.
  { right. exact denomPos. }
  split.
  - (* Inclusion of domains *)
    intros x xdf. unfold IntFn in xdf.
    assert (CRapart _ (CRpow (CR_of_Q _ (1#2)) n * CRinv _ (1 + sumAbsIFnk) (inr denomPos)) 0)
      as ddenomNonZero.
    { right. apply CRmult_lt_0_compat.
      apply pow_lt. simpl. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      apply CRinv_0_lt_compat. exact denomPos. }
    destruct (domainInfiniteSumAbsScaleIncReverse _ _ _ x xdf ddenomNonZero) as [y _].
    exact (injF x y).
  - (* Majoration of the abs integral *)
    unfold IntAbsSum.
    rewrite CRmult_comm. rewrite <- (CRmult_1_r (CRpow (CR_of_Q _ (1 # 2)) n)).
    do 2 rewrite CRmult_assoc.
    apply CRmult_le_compat_l. apply CRlt_asym, pow_lt.
    simpl. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    rewrite CRmult_1_l. apply CRlt_asym.
    apply (CRmult_lt_reg_l (1+sumAbsIFnk)). assumption.
    rewrite <- CRmult_assoc. rewrite CRinv_r.
    rewrite CRmult_1_r. rewrite CRmult_1_l.
    rewrite <- (CRplus_0_l sumAbsIFnk).
    rewrite <- CRplus_assoc. apply CRplus_lt_compat_r.
    rewrite CRplus_0_r. apply CRzero_lt_one.
Qed.

Lemma partialApplyEq
  : forall {R : ConstructiveReals} (X : Set)
           (f g : @PartialFunction R X)
           (x : X) (xD : Domain f x) (xG : Domain g x),
    f = g
    -> (partialApply f x xD == partialApply g x xG).
Proof.
  intros. subst g. apply DomainProp.
Qed.

Definition domainInfiniteSumAbsDiag
           {R : ConstructiveReals } (X : Set)
           (fnk : nat -> nat -> @PartialFunction R X)
           (n : nat)
  : DomainInclusion (XinfiniteSumAbs (diagSeq fnk))
                    (XinfiniteSumAbs (fnk n)).
Proof.
  intros x xdf.
  assert (forall k, (let (n, k) := diagPlaneInv (diagPlane n k) in fnk n k)
          = (fnk n k)) as H.
  { intro k. rewrite diagPlaneInject. reflexivity. }
  assert (forall k:nat, Domain (fnk n k) x) as xLine.
  { intro k. destruct xdf as [xn _].
    unfold diagSeq in xn. specialize (H k).
    specialize (xn (diagPlane n k)). rewrite H in xn. exact xn. }
  destruct xdf as [xnDiag cvDiag].
  assert (forall a b:nat, lt a b -> lt (diagPlane n a) (diagPlane n b)).
  { intros. unfold diagPlane. apply plus_lt_le_compat. assumption.
    apply Nat.div_le_mono. auto. apply mult_le_compat.
    apply plus_le_compat. apply le_refl. unfold lt in H0.
    apply (le_trans _ (S a)). apply le_S. apply le_refl. assumption.
    apply le_n_S. apply plus_le_compat. apply le_refl. unfold lt in H0.
    apply (le_trans _ (S a)). apply le_S. apply le_refl. assumption. }
  pose proof (CR_complete R _ cvDiag) as [lim cvlim].
  destruct (SubSeriesCv (fun k : nat =>
                CRabs _ (partialApply (diagSeq fnk k) x (xnDiag k)))
                        (exist _ (fun k => diagPlane n k) H0) lim)
    as [y i].
  apply cvlim. intros. apply CRabs_pos.
  simpl in i.
  apply (domainInfiniteSumAbsInc _ x xLine y).
  apply (series_cv_eq (fun n0 : nat =>
         CRabs _
           (partialApply (diagSeq fnk (diagPlane n n0)) x
              (xnDiag (diagPlane n n0))))).
  - intros. apply CRabs_morph. apply partialApplyEq.
    unfold diagSeq. rewrite (diagPlaneInject n n0). reflexivity.
  - exact i.
Qed.

Lemma InfiniteDiagApply
  : forall {R : ConstructiveReals } (X : Set)
      (fnk : nat -> nat -> @PartialFunction R X)
      (x : X)
      (xD : Domain (XinfiniteSumAbs (diagSeq fnk)) x),
    series_cv
      (diagSeq (fun n k : nat => CRabs _ (partialApply (fnk n k) x
                                                 (domainInfiniteSumAbsIncReverse
                                                    (fnk n) x
                                                    (domainInfiniteSumAbsDiag
                                                       X fnk n x xD) k))))
      (let (xn,a) := xD in
       let (lim,_) := CR_complete R _ a in lim).
Proof.
  intros. destruct xD as [xn cv].
  destruct (CR_complete R
         (CRsum
            (fun k : nat =>
             CRabs _ (partialApply (diagSeq fnk k) x (xn k)))) cv).
  apply (series_cv_eq (fun k : nat =>
                                CRabs _ (partialApply (diagSeq fnk k)
                                                   x (xn k)))).
  2: apply c.
  intro n.
  transitivity (let (n0,k) := diagPlaneInv n in
                          CRabs _ (partialApply (diagSeq fnk (diagPlane n0 k)) x (xn (diagPlane n0 k)))).
  - destruct (diagPlaneInv n) eqn:desN.
    apply CRabs_morph. apply partialApplyEq. unfold diagSeq. rewrite diagPlaneInject.
    rewrite desN. reflexivity.
  - assert (forall unk vnk : nat -> nat -> CRcarrier R,
               (forall n k : nat, unk n k == vnk n k)
               -> forall n:nat, diagSeq unk n == diagSeq vnk n).
    { intros. unfold diagSeq. destruct (diagPlaneInv n0). apply H. }
    apply H. clear n. intros. apply CRabs_morph.
    apply partialApplyEq. unfold diagSeq. rewrite diagPlaneInject. reflexivity.
Qed.

(* The infinite sum of lines is equal to
   the infinite diagonal sum *)
Lemma applyInfiniteSumAbsDiag
  : forall {R : ConstructiveReals } (X : Set)
      (fnk : nat -> nat -> @PartialFunction R X)
      (x : X)
      (xD : Domain (XinfiniteSumAbs (diagSeq fnk)) x),
    series_cv (fun n:nat => let (ln,a) := domainInfiniteSumAbsDiag X fnk n x xD in
                              let (lim,_) := CR_complete R _ a in
                              lim)
                     (let (xn,a) := xD in
                      let (lim,_) := CR_complete R _ a in lim).
Proof.
  intros.
  destruct (DiagSeqInfiniteSum
           (fun n k => CRabs _ (partialApply (fnk n k) x
                                       (domainInfiniteSumAbsIncReverse
                                          _ x (domainInfiniteSumAbsDiag
                                                 X fnk n x xD) k)))
           (fun n : nat =>
     let (ln, a) := domainInfiniteSumAbsDiag X fnk n x xD in
     let (lim, _) :=
       CR_complete R (CRsum (fun n0 : nat => CRabs _ (partialApply (fnk n n0) x (ln n0)))) a in
     lim)
           (let (xn,a) := xD in
              let (lim,_) := CR_complete R _ a in lim)).
  - apply (series_cv_eq (diagSeq (fun n k : nat => CRabs _
                                                   (partialApply (fnk n k) x
             (domainInfiniteSumAbsIncReverse (fnk n) x
                                             (domainInfiniteSumAbsDiag X fnk n x xD) k))))).
    intro n. unfold diagSeq. destruct (diagPlaneInv n).
    symmetry. rewrite CRabs_right. reflexivity. apply CRabs_pos.
    apply InfiniteDiagApply.
  - (* The sum on each line *)
    intro n. destruct (domainInfiniteSumAbsDiag X fnk n); simpl.
    destruct (CR_complete R (CRsum (fun k : nat => CRabs _ (partialApply (fnk n k) x (x0 k)))) c).
    exact c0.
  - destruct p, p.
    apply (CR_cv_proper _ _ _ s). symmetry.
    apply (series_cv_unique _ _ _ (InfiniteDiagApply _ _ x xD) s0).
Qed.

(* If a subset A contains a countable intersection of domains
   of integrable functions, then it is full. *)
Lemma CountableIntersectionIsFull
  : forall {IS : IntegrationSpace}
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n))
      (A : X (ElemFunc IS) -> Type),
    (forall x : X (ElemFunc IS),
        (forall n:nat, Domain (fn n) x) -> A x)
    -> almost_everywhere A.
Proof.
  intros IS fn fnInt A inc.
  pose (fun n => IntFn (let (df,_) := countable_representation IS (fn n) (fnInt n) n in df))
    as fnk.
  exists (XinfiniteSumAbs (diagSeq fnk)).
  split.
  - pose (fun n => IntFnL (let (df,_) := countable_representation IS (fn n) (fnInt n) n in df))
      as fnkL.
    destruct (series_cv_maj (fun n => IntAbsSum (let (df,_) :=
                                                  countable_representation
                                                    IS (fn n) (fnInt n) n in df))
                            (fun n => (CRpow (CR_of_Q _ (1#2)) n)) (CR_of_Q _ 2)) as [sumI cvI].
    + intro n. destruct (countable_representation IS (fn n) (fnInt n) n). simpl.
      destruct p. rewrite CRabs_right. assumption. destruct x.
      simpl. apply (series_cv_nonneg (fun k : nat => Iabs (IntFn k) (IntFnL k))).
      intros. apply integralPositive. intros x xdf.
      rewrite applyXabs. apply CRabs_pos.
      assumption.
    + apply GeoHalfTwo.
    + assert (series_cv (fun k : nat =>
       Iabs (diagSeq fnk k) (diagSeqL IS fnk fnkL k)) sumI) as H.
      apply (series_cv_eq (diagSeq (fun n k =>
                                           let (fInt,g) := countable_representation
                                                          IS (fn n) (fnInt n) n in
                                           Iabs (IntFn fInt k) (IntFnL fInt k)))).
      intro n. unfold diagSeq, diagSeqL. destruct (diagPlaneInv n).
      unfold fnk, fnkL.
      destruct (countable_representation IS (fn n0) (fnInt n0) n0).
      reflexivity.
      apply (DiagSeqInfiniteSumColPos
               _ (fun n => IntAbsSum (let (df,_) := countable_representation
                                                   IS (fn n) (fnInt n) n in df))).
      intros. destruct (countable_representation IS (fn n) (fnInt n) n).
      apply integralPositive. intros y ydf. rewrite applyXabs.
      apply CRabs_pos. intro n.
      destruct (countable_representation IS (fn n) (fnInt n) n).
      destruct x. assumption. apply cvI.
      exists (Build_IntegralRepresentation
           IS
                (diagSeq fnk)
                (diagSeqL IS fnk fnkL)
                sumI H).
      apply PartialRestriction_refl.
  - (* Inclusion of domains *)
    intros xDiag xdf. apply inc.
    clear inc. intro n. simpl.
    pose proof (domainInfiniteSumAbsDiag _ fnk n xDiag xdf) as H.
    unfold fnk in H.
    destruct (countable_representation IS (fn n) (fnInt n) n) as [[fnn] [i _]].
    unfold IntFn in i. apply i, H.
Qed.

Lemma IntegralNonDecreasingAE
  : forall {IS : IntegrationSpace}
      (f g : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (gInt : IntegrableFunction g),
    almost_everywhere
      (fun x : X (ElemFunc IS)
       => forall (dF : Domain f x) (dG : Domain g x),
           partialApply _ _ dF <= partialApply _ _ dG)
    -> Integral fInt <= Integral gInt.
Proof.
  intros. destruct X as [h [hInt inc]].
  pose proof (IntegralNonDecreasing
                (Xplus f (Xminus h h))
                (Xplus g (Xminus h h))
                (IntegrablePlus f (Xminus h h) fInt
                                (IntegrableMinus h h hInt hInt))
                (IntegrablePlus g (Xminus h h) gInt
                                (IntegrableMinus h h hInt hInt))).
  rewrite IntegralPlus in H. rewrite IntegralPlus in H.
  rewrite IntegralMinus in H. unfold CRminus in H.
  rewrite CRplus_opp_r, CRplus_0_r, CRplus_0_r in H. apply H.
  intros x xdf xdg. destruct xdf, xdg.
  rewrite (applyXplus f (Xminus h h)), (applyXplus g (Xminus h h)).
  destruct d0, d2.
  rewrite (applyXminus h h), (applyXminus h h).
  destruct f,g,h; simpl; clear H gInt fInt. simpl in inc.
  rewrite (DomainProp1 _ d3 d0), (DomainProp1 _ d2 d0), (DomainProp1 _ d4 d0).
  unfold CRminus. rewrite CRplus_opp_r, CRplus_0_r, CRplus_0_r.
  apply inc. apply d2.
Qed.

Lemma IntegralExtensionalAE
  : forall {IS : IntegrationSpace}
      (f g : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (gInt : IntegrableFunction g),
    almost_everywhere
      (fun x : X (ElemFunc IS)
       => forall (dF : Domain f x) (dG : Domain g x),
           partialApply _ _ dF == partialApply _ _ dG)
    -> Integral fInt == Integral gInt.
Proof.
  intros. split.
  - apply IntegralNonDecreasingAE. destruct X as [h [hInt p]].
    exists h. split. exact hInt.
    intros x dfull dG dF.
    rewrite (p x dfull dF dG). apply CRle_refl.
  - apply IntegralNonDecreasingAE. destruct X as [h [hInt p]].
    exists h. split. exact hInt.
    intros x dfull dF dG. rewrite (p x dfull dF dG).
    apply CRle_refl.
Qed.

Definition PackFirstFunctions {R : ConstructiveReals } (X : Set)
           (fn : nat -> @PartialFunction R X)
           (n p : nat) : PartialFunction X
  := match p with
     | O => Xsum fn n
     | _ => fn (n + p)%nat
     end.

Lemma PackFirstFunctionsL : forall (IS : IntegrationSpace)
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
           (fnL : forall n:nat, L (ElemFunc IS) (fn n))
           (n p : nat),
    L (ElemFunc IS) (PackFirstFunctions (X (ElemFunc IS)) fn n p).
Proof.
  intros. unfold PackFirstFunctions. destruct p.
  - apply LsumStable. apply fnL.
  - apply fnL.
Defined.

Lemma applyPackFirstSum : forall {R : ConstructiveReals} (X : Set)
           (fn : nat -> @PartialFunction R X)
           (n N : nat)
           (x : X)
           (pxDn : forall n:nat, Domain (fn n) x)
           (pxDnP : forall n:nat, Domain (PackFirstFunctions X fn N n) x),
    (CRsum (fun k => partialApply (PackFirstFunctions X fn N k) x (pxDnP k)) n
     == CRsum (fun k => partialApply (fn k) x (pxDn k)) (n+N)).
Proof.
  induction n.
  - intros. simpl. rewrite (applyXsum _ _ _ (pxDnP O) pxDn). reflexivity.
  - intros. simpl. rewrite (IHn N x pxDn). clear IHn. apply CRplus_morph.
    reflexivity. replace (S (n + N)) with (N + S n)%nat.
    apply DomainProp. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma IabsMinusMaj : forall (IS : IntegrationSpace)
                       (f g : PartialFunction (X (ElemFunc IS)))
                       (fL : L (ElemFunc IS) f)
                       (gL : L (ElemFunc IS) g),
    - Iabs f fL + Iabs g gL
    <= Iabs (Xminus f g) (LminusStable f g fL gL).
Proof.
  intros. rewrite CRplus_comm. unfold Iabs.
  pose proof (@Iminus IS).
  unfold CRminus in H. rewrite <- H. clear H.
  apply INonDecreasing. intros. destruct y.
  rewrite applyXabs. rewrite (applyXminus f g).
  destruct xF. rewrite (applyXminus (Xabs g) (Xabs f)).
  unfold Xabs, Xop, partialApply.
  destruct f,g.
  rewrite (DomainProp0 x d0 d1), (DomainProp x d2 d).
  rewrite CRabs_minus_sym.
  apply CRabs_triang_inv.
Qed.

Lemma PackSeriesCV : forall {R : ConstructiveReals}
                       (un : nat -> CRcarrier R) (N : nat) (a s : CRcarrier R),
    series_cv un s
    -> series_cv (fun n => match n with
                          | O => a
                          | _ => un (N + n)%nat
                          end) (s - CRsum un N + a).
Proof.
  intros. intros n. specialize (H n) as [k maj].
  exists k. (* same modulus of convergence *)
  intros i H. destruct i.
  - inversion H. subst k. simpl. clear H.
    rewrite <- (CRplus_comm a). unfold CRminus.
    rewrite CRopp_plus_distr. rewrite <- CRplus_assoc. rewrite CRplus_opp_r.
    rewrite CRplus_0_l. rewrite CRabs_opp.
    specialize (maj N (le_0_n N)).
    rewrite CRabs_minus_sym in maj. exact maj.
  - rewrite decomp_sum. simpl. unfold CRminus.
    rewrite CRplus_comm. rewrite CRopp_plus_distr.
    rewrite CRplus_assoc.
    rewrite <- (CRplus_assoc (-a)). rewrite CRplus_opp_l.
    rewrite CRplus_0_l.
    rewrite CRopp_plus_distr. rewrite CRopp_involutive.
    rewrite (CRsum_eq (fun i : nat => un (N + S i)%nat) (fun i : nat => un (S N + i)%nat)).
    rewrite CRplus_assoc.
    rewrite <- sum_assoc. rewrite CRplus_comm. simpl in maj. apply maj.
    apply (le_trans k (S i)). assumption. simpl.
    apply le_n_S. rewrite plus_comm. rewrite <- (plus_0_r i). rewrite <- plus_assoc.
    apply Nat.add_le_mono_l. apply le_0_n.
    intros. rewrite Nat.add_succ_r. reflexivity. apply le_n_S.
    apply le_0_n.
Qed.

Lemma PackSeriesCVReverse
  : forall {R : ConstructiveReals} (un : nat -> CRcarrier R)
           (N : nat) (a s : CRcarrier R),
    series_cv (fun n => match n with
                        | O => a
                        | _ => un (N + n)%nat
                        end) s
    -> series_cv un (s - a + CRsum un N).
Proof.
  intros. intros eps. specialize (H eps) as [k maj].
  exists (S N + k)%nat. (* translated same modulus of convergence *)
  intros n kLen.
  destruct (Nat.le_exists_sub (S N) n) as [m [inf _]].
  apply (le_trans _ (S N + k)). rewrite <- (plus_0_r (S N)).
  rewrite <- plus_assoc. apply Nat.add_le_mono_l. apply le_0_n.
  assumption.
  subst n. replace (m + S N)%nat with (S N + m)%nat. rewrite sum_assoc.
  specialize (maj (S m)). rewrite decomp_sum in maj.
  simpl in maj. unfold CRminus. simpl.
  rewrite CRplus_comm.
  rewrite CRopp_plus_distr, CRplus_assoc. simpl.
  rewrite <- (CRplus_assoc (-CRsum un N)).
  rewrite CRplus_opp_l. rewrite CRplus_0_l.
  rewrite (CRplus_comm s). rewrite CRopp_plus_distr.
  rewrite CRopp_involutive. rewrite CRplus_assoc.
  rewrite (CRplus_comm (-s)). rewrite <- CRplus_assoc.
  rewrite (CRsum_eq _ (fun i : nat => un (N + S i)%nat)). apply maj.
  rewrite plus_comm in kLen. apply Nat.add_le_mono_r in kLen.
  apply (le_trans k m). assumption. apply le_S. apply le_refl.
  intros. rewrite Nat.add_succ_r. reflexivity. apply le_n_S.
  apply le_0_n. rewrite plus_comm. reflexivity.
Qed.

Definition domainSumPackIncReverse
           {R : ConstructiveReals} (X : Set)
           (fn : nat -> @PartialFunction R X)
           (N : nat)
           (x : X)
           (xn : forall n:nat, Domain (PackFirstFunctions X fn N n) x)
  : forall n:nat, Domain (fn n) x.
Proof.
  intros. destruct (le_lt_dec n N).
  - exact (domainXsumIncReverse fn n N x (xn O) l).
  - pose (xn (n - N)%nat). unfold PackFirstFunctions in d.
    destruct (n - N)%nat eqn:des. exfalso. apply (Nat.sub_gt n N); assumption.
    rewrite <- (Nat.sub_add N n). rewrite des. rewrite plus_comm.
    exact d. subst d.
    apply (le_trans N (S N)). apply le_S. apply le_refl. assumption.
Qed.

Definition domainInfiniteSumPackInc
           {R : ConstructiveReals} (X : Set)
           (fn : nat -> @PartialFunction R X)
           (N : nat)
  : PartialRestriction (XinfiniteSumAbs (PackFirstFunctions X fn N))
                       (XinfiniteSumAbs fn).
Proof.
  split.
  - intros x xD.
    (* The absolute convergence, to the adjusted limit *)
    apply (domainInfiniteSumAbsInc
             fn x
             (fun k => domainSumPackIncReverse
                      X fn N x (fun n => domainInfiniteSumAbsIncReverse _ x xD n) k)
             (let (xn,a) := xD in
              let (lim,_) := CR_complete R _ a in
              lim
              - CRabs _ (partialApply _ x (domainInfiniteSumAbsIncReverse _ x xD 0))
              + CRsum (fun k => CRabs _ (partialApply _ x (domainSumPackIncReverse X fn N x (fun n => domainInfiniteSumAbsIncReverse _ x xD n) k))) N
          )).
    destruct xD as [xn cv2]; simpl.
    destruct (CR_complete R
                (CRsum
                   (fun n : nat =>
                      CRabs _ (partialApply (PackFirstFunctions X fn N n) x (xn n)))) cv2)
      as [sumAbsXn cv].
    apply PackSeriesCVReverse.
    apply (series_cv_eq (fun n : nat => CRabs _ (partialApply _ x (xn n)))).
    2: apply cv.
    intro n. unfold PackFirstFunctions.
    destruct n. reflexivity.
    apply CRabs_morph. apply DomainProp.
  - intros. (* The direct convergence, to the same limit *)
    destruct xD,xG; simpl.
    destruct (series_cv_abs (fun n : nat => partialApply (PackFirstFunctions X fn N n) x (x0 n)) c).
    destruct (series_cv_abs (fun n : nat => partialApply (fn n) x (x1 n)) c0).
    apply (series_cv_unique (fun k : nat => partialApply (fn k) x (x1 k))).
    2: apply s0.
    intros eps.
    specialize (s eps) as [k maj].
    exists (S N + k)%nat. (* translated modulus of convergence *)
    intros n H0. destruct (Nat.le_exists_sub N n) as [m [inf _]].
    apply (le_trans _ (S N + k)).
    simpl. apply le_S. rewrite <- (plus_0_r N).
    rewrite <- plus_assoc. apply Nat.add_le_mono_l.
    apply le_0_n. assumption. subst n.
    rewrite <- (applyPackFirstSum X fn m N x x1 x0).
    apply maj. apply (Nat.add_le_mono_l k m (S N)).
    apply (le_trans _ (m + N)). assumption. rewrite plus_comm.
    apply Nat.add_le_mono_r. apply le_S. apply le_refl.
Qed.

(* Lemma 1.15 in Bishop's article, a representation
   that fits the absolute integral better. *)
Lemma AbsRepresentation : forall (IS : IntegrationSpace)
                            (f : PartialFunction (X (ElemFunc IS)))
                            (eps : CRcarrier (RealT (ElemFunc IS)))
                            (fInt : IntegrableFunction f),
    0 < eps
    -> { intRepres : IntegralRepresentation
        & prod (PartialRestriction (XinfiniteSumAbs (IntFn intRepres)) f)
               (IntAbsSum intRepres
                <= Integral (IntegrableAbs f fInt) + eps) }.
Proof.
  intros.
  pose proof (IntegralAbsLimit f fInt) as IabsLimit.
  destruct fInt as [[fn fnL sumIAbsFn lim] [inj restr]] eqn:desFint.
  unfold IntFn, IntFnL in IabsLimit. unfold IntFn in inj, restr.
  assert (forall N:nat, series_cv
    (fun k : nat =>
       Iabs (PackFirstFunctions (X (ElemFunc IS)) fn N k)
            (PackFirstFunctionsL IS fn fnL N k))
    (sumIAbsFn - CRsum (fun n : nat => Iabs (fn n) (fnL n)) N +
     Iabs (Xsum fn N) (LsumStable fn fnL N)))
    as limPack.
  { intro N.
    apply (series_cv_eq
             (fun n => match n with
                       | O => Iabs (Xsum fn N) (LsumStable  fn fnL N)
                       | _ => Iabs (fn (N+n)%nat) (fnL (N+n)%nat)
                       end)).
    intro n. destruct n; reflexivity.
    apply (PackSeriesCV (fun n : nat => Iabs (fn n) (fnL n))).
    assumption. }
  pose (fun N:nat => Build_IntegralRepresentation
                  IS
            (PackFirstFunctions (X (ElemFunc IS)) fn N)
            (PackFirstFunctionsL IS fn fnL N)
            (sumIAbsFn
             - CRsum (fun n => Iabs (fn n) (fnL n)) N
             + Iabs (Xsum fn N) (LsumStable fn fnL N))
            (limPack N))
    as represPack.
  assert (forall N:nat, PartialRestriction (XinfiniteSumAbs (IntFn (represPack N))) f)
    as IsRepresPack.
  { intro N. unfold represPack, IntFn.
    destruct (domainInfiniteSumPackInc (X (ElemFunc IS)) fn N) as [inc app].
    split. intros x xdf.
    apply inj, inc. exact xdf.
    intros. specialize (app x xD (inc x xD)). rewrite app.
    apply restr. }

  destruct (CRup_nat (CR_of_Q _ 2 * CRinv _ eps (inr H))) as [epsN majEpsN].
  pose proof (lim (Pos.of_nat epsN)) as [N limN].
  exists (represPack N). split. apply IsRepresPack.

  (* Prove the epsilon majoration *)
  apply (CRle_trans _ (Iabs (Xsum fn N) (LsumStable fn fnL N)
                       + eps * CR_of_Q _ (1#2))).
  - simpl. specialize (limN N (le_refl N)).
    rewrite <- (CRplus_comm (eps * CR_of_Q _ (1#2))).
    apply CRplus_le_compat. 2: apply CRle_refl.
    rewrite CRabs_minus_sym in limN.
    apply (CRle_trans
             _ (CRabs _ (sumIAbsFn - CRsum (fun k : nat => Iabs (fn k) (fnL k)) N))).
    apply CRle_abs. apply (CRle_trans _ (CR_of_Q _ (1# Pos.of_nat epsN))).
    assumption. apply (CRmult_lt_compat_r eps) in majEpsN.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r in majEpsN.
    2: exact H. apply CRlt_asym.
    apply (CRmult_lt_reg_r (CR_of_Q _ 2)).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
    rewrite CRmult_assoc, <- (CR_of_Q_mult _ (1#2)).
    setoid_replace ((1 # 2) * 2)%Q with 1%Q.
    2: reflexivity. rewrite CR_of_Q_one, CRmult_1_r.
    apply (CRmult_lt_reg_l (CR_of_Q _ (Z.pos (Pos.of_nat epsN) #1))).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
    rewrite <- CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((Z.pos (Pos.of_nat epsN) # 1) * (1 # Pos.of_nat epsN))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_l. apply (CRlt_le_trans _ _ _ majEpsN).
    apply CRmult_le_compat_r. apply CRlt_asym, H.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. destruct epsN. discriminate.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite SuccNat2Pos.id_succ, Nat2Pos.id. apply le_refl. discriminate.
    unfold Qmult, Qeq, Qnum, Qden. do 2 rewrite Z.mul_1_r. reflexivity.
  - (* Replace the limit at infinity by a finite m > N *)
    apply (CR_cv_bound_down
             (fun m => Iabs (Xsum fn m) (LsumStable fn fnL m) + eps) _ _ (S N)).
    intros m maj.
    apply (CRplus_le_reg_l (- Iabs (Xsum fn m) (LsumStable fn fnL m))).
    rewrite <- CRplus_assoc. rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
    rewrite CRplus_0_l. apply (CRplus_le_reg_r (- (eps * CR_of_Q _ (1#2)))).
    rewrite CRplus_assoc. rewrite CRplus_opp_r. rewrite CRplus_0_r.
    apply (CRle_trans _ (Iabs (Xminus (Xsum fn m) (Xsum fn N))
                              (LminusStable _ _ (LsumStable fn fnL m)
                                            (LsumStable fn fnL N)))).
    apply IabsMinusMaj.
    destruct (Nat.le_exists_sub N m) as [k [add _]]. apply le_S in maj.
    apply le_S_n in maj. assumption. subst m. destruct k.
    exfalso. exact (lt_irrefl N maj).
    apply (CRle_trans
             _ (Iabs (Xsum (fun a => fn (S N + a)%nat) k)
                     (LsumStable (fun a => fn (S N + a)%nat)
                                 (fun a => fnL (S N + a)%nat) k))).
    apply INonDecreasing.
    intros. rewrite applyXabs. rewrite applyXabs.
    remember (S k + N)%nat. rewrite plus_comm in Heqn.
    replace (N + S k)%nat with (S N + k)%nat in Heqn. subst n.
    rewrite (Xsum_assocMinus fn N k x _ y).
    apply CRle_refl. rewrite Nat.add_succ_r. reflexivity.
    apply (CRle_trans
             _ (I IS (Xsum (fun a : nat => Xabs (fn (S N + a)%nat)) k)
                  (LsumStable _ (fun a => LabsStable (ElemFunc IS) (fn (S N + a)%nat)
                                                  (fnL (S N + a)%nat)) k))).
    apply INonDecreasing. intros.
    apply XmultiTriangleIneg. rewrite IadditiveIterate.
    rewrite <- (CRsum_eq (fun n0 : nat =>
                         I IS (Xabs (fn (N + S n0)%nat))
                           (LabsStable (ElemFunc IS) (fn (N + S n0)%nat) (fnL (N + S n0)%nat)))).
    apply (series_cv_remainder_maj (fun n0 : nat =>
                                    I IS (Xabs (fn n0))
                                      (LabsStable (ElemFunc IS) (fn n0) (fnL n0))) sumIAbsFn).
    apply lim.
    rewrite <- (CRplus_opp_r (eps * CR_of_Q _ (1 # 2))).
    apply CRplus_lt_compat_r.
    rewrite <- (CRmult_1_r eps).
    rewrite CRmult_assoc. apply CRmult_lt_compat_l.
    assumption. rewrite CRmult_1_l. apply (CRmult_lt_reg_l (CR_of_Q _ 2)).
    rewrite <- CR_of_Q_zero.
    apply CR_of_Q_lt; reflexivity. rewrite <- CR_of_Q_mult.
    rewrite CRmult_1_r. apply CR_of_Q_lt. reflexivity.
    intro n. apply integralPositive. intros x xdf. rewrite applyXabs.
    apply CRabs_pos. apply CRlt_asym.
    setoid_replace (eps + - (eps * CR_of_Q _ (1 # 2)))
      with (eps * CR_of_Q _ (1 # 2)).
    apply (CRmult_lt_compat_r eps) in majEpsN.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r in majEpsN.
    2: exact H.
    apply (CRle_lt_trans _ (CR_of_Q _ (1 # Pos.of_nat epsN))).
    apply limN. apply le_refl.
    apply (CRmult_lt_reg_r (CR_of_Q _ 2)).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
    rewrite CRmult_assoc, <- (CR_of_Q_mult _ (1#2)).
    setoid_replace ((1 # 2) * 2)%Q with 1%Q.
    2: reflexivity. rewrite CR_of_Q_one, CRmult_1_r.
    apply (CRmult_lt_reg_l (CR_of_Q _ (Z.pos (Pos.of_nat epsN) #1))).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
    rewrite <- CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((Z.pos (Pos.of_nat epsN) # 1) * (1 # Pos.of_nat epsN))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_l. apply (CRlt_le_trans _ _ _ majEpsN).
    apply CRmult_le_compat_r. apply CRlt_asym, H.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. destruct epsN. discriminate.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite SuccNat2Pos.id_succ, Nat2Pos.id. apply le_refl. discriminate.
    unfold Qmult, Qeq, Qnum, Qden. do 2 rewrite Z.mul_1_r. reflexivity.
    rewrite <- (CRmult_1_r eps), CRopp_mult_distr_r.
    rewrite CRmult_assoc, <- CRmult_plus_distr_l.
    apply CRmult_morph. rewrite CRmult_1_r. reflexivity. rewrite CRmult_1_l.
    rewrite <- CR_of_Q_opp, <- CR_of_Q_one, <- CR_of_Q_plus.
    apply CR_of_Q_morph. reflexivity.
    intros. rewrite Nat.add_succ_r. reflexivity.
    apply CR_cv_plus. assumption. apply CR_cv_const.
Qed.

(* We now state the completeness theorem of integrable functions of an integration
   space IS : they behave as the L-functions of a bigger integration space,
   which integrable functions are already integrable in IS. *)

Definition CompleteRepresentation
           (IS : IntegrationSpace)
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
           (fnInt : forall n:nat, IntegrableFunction (fn n))
  : { intRepresN : nat -> IntegralRepresentation
      & forall n:nat, prod (PartialRestriction
                       (XinfiniteSumAbs (IntFn (intRepresN n))) (fn n))
                    (IntAbsSum (intRepresN n)
                     <= Integral (IntegrableAbs (fn n) (fnInt n))
                       + CRpow (CR_of_Q _ (1#2)) n) }.
Proof.
  assert (0 < CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) as halfPos.
  { rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. }
  exists (fun n:nat => let (df,_) := AbsRepresentation
       IS (fn n) (CRpow (CR_of_Q _ (1#2)) n) (fnInt n)
       (pow_lt (CR_of_Q _ (1 # 2)) n halfPos) in df).
  intro n. destruct (AbsRepresentation
       IS (fn n) _ (fnInt n)
       (pow_lt (CR_of_Q _ (1 # 2)) n halfPos)).
  simpl. split; apply p.
Qed.

Lemma CompleteRepresentationDoubleSum
  : forall (IS : IntegrationSpace)
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n)),
    let (intRepresN, _) := CompleteRepresentation IS fn fnInt in
    forall (x : X (ElemFunc IS)) (xD : Domain
        (XinfiniteSumAbs
           (diagSeq
              (fun n k : nat => IntFn (intRepresN n) k))) x)
      (pxF : forall n : nat, Domain (fn n) x),
      series_cv
        (fun n : nat => partialApply (fn n) x (pxF n))
        (partialApply (XinfiniteSumAbs (diagSeq
                                               (fun n k : nat => IntFn (intRepresN n) k))) x xD).
Proof.
  intros. destruct (CompleteRepresentation IS fn fnInt) as [cfnInt represN].
  intros.
  destruct (DiagSeqInfiniteSum
           (fun n k => partialApply _ _
                                    (domainInfiniteSumAbsIncReverse
                                       _ x (domainInfiniteSumAbsDiag _ _ n x xD) k))
           (fun n : nat => partialApply (fn n) x (pxF n))
           (let (xn,a) := xD in
            let (l,_) := CR_complete _ _ a in l)).
  - apply InfiniteDiagApply.
  - (* The limit on each line *)
    intro n. apply represApply. apply represN.
  - setoid_replace (partialApply
       (XinfiniteSumAbs
          (diagSeq (fun n k : nat => IntFn (cfnInt n) k))) x xD)
      with x0.
    apply p. destruct p,p.
    apply (series_cv_unique (diagSeq
            (fun n k : nat =>
             partialApply (IntFn (cfnInt n) k) x
               (domainInfiniteSumAbsIncReverse (fun k0 : nat => IntFn (cfnInt n) k0) x
                  (domainInfiniteSumAbsDiag (X (ElemFunc IS))
                                            (fun n0 k0 : nat => IntFn (cfnInt n0) k0) n x xD) k)))).
    2: exact s0.
    apply (series_cv_eq (fun k : nat =>
           partialApply
             (diagSeq (fun n k0 : nat => IntFn (cfnInt n) k0) k) x
             (let (xn,_) := xD in xn k))).
    + intro n.
      transitivity (let (n0,k) := diagPlaneInv n in
     partialApply (IntFn (cfnInt n0) k) x
       (domainInfiniteSumAbsIncReverse (fun k0 : nat => IntFn (cfnInt n0) k0) x
               (domainInfiniteSumAbsDiag (X (ElemFunc IS)) (fun n1 k0 : nat => IntFn (cfnInt n1) k0)
                                       n0 x xD) k)).
      2: reflexivity. destruct (diagPlaneInv n) eqn:desN.
      apply partialApplyEq. unfold diagSeq. rewrite desN. reflexivity.
    + destruct xD as [xn cv]; simpl. apply series_cv_abs_cv.
Qed.

Lemma partialInfiniteTriangle
  : forall {R : ConstructiveReals} (X : Set)
           (fn : nat -> @PartialFunction R X) (x : X)
      (xD : Domain (XinfiniteSumAbs fn) x),
    CRle _ (CRabs _ (partialApply _ x xD))
        (let (xn, cv) := xD in
         let (l,_) := CR_complete R _ cv in l).
Proof.
  intros. destruct xD as [xn limAbs]; simpl.
  destruct (series_cv_abs (fun n : nat => partialApply (fn n) x (xn n)) limAbs).
  apply (series_cv_triangle (fun k : nat => partialApply (fn k) x (xn k))).
  exact s.
  destruct (CR_complete R
         (CRsum (fun n : nat => CRabs _ (partialApply (fn n) x (xn n)))) limAbs).
  exact c.
Qed.

Lemma CompleteRepresentationRestrict
  : forall (IS : IntegrationSpace)
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n)),
    let (intRepresN, _) := CompleteRepresentation IS fn fnInt in
    PartialRestriction
      (XinfiniteSumAbs
         (diagSeq (fun n k => IntFn (intRepresN n) k)))
      (XinfiniteSumAbs fn).
Proof.
  intros. pose proof (CompleteRepresentationDoubleSum IS fn fnInt) as dsum.
  destruct (CompleteRepresentation IS fn fnInt) as [intRepresN restrN].
  split. intros x xdf.
  pose (domainInfiniteSumAbsDiag
          _ (fun n k => IntFn (intRepresN n) k))
    as lineInj.

  destruct (series_cv_maj
              (fun n : nat =>
                 CRabs _ (partialApply (XinfiniteSumAbs (fun k : nat => IntFn (intRepresN n) k)) x (lineInj n x xdf)))
              (fun n => let (_,a) := lineInj n x xdf in
                        let (l,_) := CR_complete _ _ a in
                        l)
              (let (_,a) := xdf in
               let (l,_) := CR_complete _ _ a in
               l)).
  - intro n. simpl. rewrite CRabs_right.
    apply partialInfiniteTriangle. apply CRabs_pos.
  - apply applyInfiniteSumAbsDiag.
  - destruct p.
    apply (domainInfiniteSumAbsInc
             fn x (fun n:nat => fst (fst (restrN n)) x (lineInj n x xdf)) x0).
    + apply (series_cv_eq (fun n : nat =>
         CRabs _
           (partialApply
              (XinfiniteSumAbs (fun k : nat => IntFn (intRepresN n) k)) x
              (lineInj n x xdf)))).
      2: exact s. intro n. destruct (restrN n) as [[j a0] maj].
      unfold fst.
      specialize (a0 x (lineInj n x xdf)). apply CRabs_morph.
      apply a0.
  - intros. symmetry. apply applyInfiniteSumAbs. apply dsum.
Qed.

(* Theorem 1.16 of Bishop *)
Lemma IntegrableFunctionsComplete
  : forall (IS : IntegrationSpace)
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n))
      (sumIAbsFn : CRcarrier (RealT (ElemFunc IS))),
    (series_cv
       (fun k:nat => Integral (IntegrableAbs (fn k) (fnInt k)))
       sumIAbsFn)
    -> { represInt : IntegralRepresentation
            & prod (PartialRestriction (XinfiniteSumAbs (IntFn represInt))
                                       (XinfiniteSumAbs fn))
                   (series_cv (fun n => Integral (fnInt n))
                                     (IntegralSeries represInt)) }.
Proof.
  intros. pose proof (CompleteRepresentationRestrict IS fn fnInt) as complRestrict.
  destruct (CompleteRepresentation IS fn fnInt) as [intRepresN restrN].
  destruct (series_cv_maj (fun n => IntAbsSum (intRepresN n))
                          (fun n => Integral (IntegrableAbs (fn n) (fnInt n))
                                  + CRpow (CR_of_Q _ (1#2)) n)
                          (sumIAbsFn + CR_of_Q _ 2)) as [s [cvs majS]].
  - intro n. rewrite CRabs_right. apply (restrN n).
    destruct (intRepresN n); simpl.
    apply (series_cv_nonneg (fun k : nat => Iabs (IntFn k) (IntFnL k))).
    intro n0. apply integralPositive. intros x xdf. rewrite applyXabs.
    apply CRabs_pos. assumption.
  - apply series_cv_plus. apply H. apply GeoHalfTwo.
  - assert (series_cv (fun k : nat => Iabs
       (diagSeq (fun n k0 : nat => IntFn (intRepresN n) k0) k)
       (diagSeqL IS (fun n k0 : nat => IntFn (intRepresN n) k0)
                 (fun n k0 : nat => IntFnL (intRepresN n) k0) k)) s).
    { apply (series_cv_eq (diagSeq (fun n k => Iabs
       (IntFn (intRepresN n) k)
       (IntFnL (intRepresN n) k)))).
      intro n. unfold diagSeq, diagSeqL. destruct (diagPlaneInv n). reflexivity.
      apply (DiagSeqInfiniteSumColPos _ (fun n : nat => IntAbsSum (intRepresN n))).
      intros n k. apply integralPositive. intros x xdf.
      rewrite applyXabs.
      apply CRabs_pos. intro n. apply (intRepresN n). assumption. }
    exists (Build_IntegralRepresentation
         IS
         (diagSeq (fun n k => IntFn (intRepresN n) k))
         (diagSeqL IS _ (fun n k => IntFnL (intRepresN n) k))
         s H0).
    split.
    + exact complRestrict.
    + pose proof (IntegralCv {| IntFn := diagSeq
                  (fun n k : nat => IntFn (intRepresN n) k);
       IntFnL := diagSeqL IS (fun n k : nat => IntFn (intRepresN n) k)
                   (fun n k : nat => IntFnL (intRepresN n) k);
       IntAbsSum := s;
       IntAbsSumCv := H0 |}); simpl.
      simpl in H1.
      destruct (series_cv_maj
                    (diagSeq (fun n k : nat => CRabs _ (I IS _ (IntFnL (intRepresN n) k))))
                    (fun k : nat => Iabs _
            (diagSeqL IS (fun n k0 : nat => IntFn (intRepresN n) k0)
                      (fun n k0 : nat => IntFnL (intRepresN n) k0) k)) s).
      intro n. rewrite CRabs_right.
      unfold diagSeq, diagSeqL. destruct (diagPlaneInv n).
      apply integralAbsMaj. unfold diagSeq. destruct (diagPlaneInv n).
      apply CRabs_pos. assumption.

      destruct (DiagSeqInfiniteSum
               (fun n k => I IS _ (IntFnL (intRepresN n) k))
               (fun n : nat => Integral (fnInt n)) x).
      apply p.
      (* Limit on each line *)
      intro n. clear p. clear x.
      pose proof (IntegralRepresentationInvariant
                    (fn n) (existT _ (intRepresN n) (fst (restrN n))) (fnInt n)).
      rewrite <- H2.
      apply (IntegralCv (intRepresN n)).

      destruct (series_cv_maj
         (fun n : nat =>
          I IS _
            (diagSeqL IS (fun n0 k : nat => IntFn (intRepresN n0) k)
               (fun n0 k : nat => IntFnL (intRepresN n0) k) n))
         (fun k : nat =>
          Iabs _
            (diagSeqL IS (fun n k0 : nat => IntFn (intRepresN n) k0)
               (fun n k0 : nat => IntFnL (intRepresN n) k0) k)) s
         (fun n : nat =>
          integralAbsMaj _
            (diagSeqL IS (fun n0 k : nat => IntFn (intRepresN n0) k)
               (fun n0 k : nat => IntFnL (intRepresN n0) k) n)) H0).
      setoid_replace x1 with x0. apply p0.
      apply (series_cv_unique
               (diagSeq (fun n k : nat => I IS (IntFn (intRepresN n) k) (IntFnL (intRepresN n) k)))).
      2: apply p0.

      apply (series_cv_eq (fun n : nat => I IS _
           (diagSeqL IS (fun n0 k : nat => IntFn (intRepresN n0) k)
              (fun n0 k : nat => IntFnL (intRepresN n0) k) n))).
      intro n. unfold diagSeq, diagSeqL. destruct (diagPlaneInv n). reflexivity.
      assumption.
Qed.

(* Now that we have proved the completeness theorem, we can forget
   L-functions and use integrable functions everywhere instead. *)


Definition DiscrDeriv {R : ConstructiveReals} (X : Set)
           (fn : nat -> @PartialFunction R X) (n : nat)
  := match n with
     | O => fn O
     | S p => Xminus (fn n) (fn p)
     end.

Lemma DiscrDerivDomainInc : forall {R : ConstructiveReals} (X : Set)
                                   (fn : nat -> @PartialFunction R X)
                              (x : X)
                              (xn : forall n : nat, Domain (fn n) x) (n : nat),
    Domain (DiscrDeriv X fn n) x.
Proof.
  intros. unfold DiscrDeriv. destruct n. exact (xn O). split.
  apply xn. apply xn.
Qed.

Lemma DiscrDerivDomainIncReverse
  : forall {R : ConstructiveReals} (X : Set) (fn : nat -> @PartialFunction R X)
      (x : X)
      (xn : forall n : nat, Domain (DiscrDeriv X fn n) x)
      (n : nat),
    Domain (fn n) x.
Proof.
  intros. pose (xn n). unfold DiscrDeriv in d.
  destruct n. exact d.
  unfold Xminus, Xplus in d.
  exact (fst d).
Qed.

Lemma DiscrDerivApply
  : forall {R : ConstructiveReals} (X : Set)
      (fn : nat -> @PartialFunction R X)
      (x : X)
      (pxn : forall n: nat, Domain (DiscrDeriv X fn n) x)
      (n : nat)
      (px : Domain (fn n) x),
    (CRsum (fun k : nat => partialApply (DiscrDeriv X fn k) x (pxn k)) n
     == partialApply (fn n) x px).
Proof.
  induction n.
  - intros. simpl. apply DomainProp.
  - intros.
    transitivity (CRsum (fun k : nat => partialApply (DiscrDeriv X fn k) x (pxn k)) n
                  + partialApply (DiscrDeriv X fn (S n)) x (pxn (S n))).
    reflexivity.
    pose proof (DiscrDerivDomainIncReverse X fn x pxn n) as H.
    specialize (IHn H). rewrite IHn. clear IHn.
    unfold DiscrDeriv. destruct (pxn (S n)).
    rewrite (applyXminus (fn (S n)) (fn n)).
    rewrite (DomainProp (fn (S n)) x d px).
    rewrite (DomainProp (fn n) x d0 H).
    rewrite CRplus_comm. unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l.
    rewrite CRplus_0_r. reflexivity.
Qed.

Definition IntegrableDiscrDeriv (IS : IntegrationSpace)
                              (fn : nat -> PartialFunction (X (ElemFunc IS)))
                              (fnInt : forall n:nat, IntegrableFunction (fn n))
                              (n : nat)
  : IntegrableFunction (DiscrDeriv (X (ElemFunc IS)) fn n).
Proof.
  intros. destruct n. apply fnInt. apply IntegrableMinus; apply fnInt.
Defined.

Lemma SumDiscrDeriv
  : forall (IS : IntegrationSpace)
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n))
      (n : nat),
    CRsum
      (fun k : nat => Integral (IntegrableDiscrDeriv IS fn fnInt k)) n
    == Integral (fnInt n).
Proof.
  induction n.
  - reflexivity.
  - replace (CRsum (fun k : nat => Integral (IntegrableDiscrDeriv IS fn fnInt k)) (S n))
      with (CRsum (fun k : nat => Integral (IntegrableDiscrDeriv IS fn fnInt k)) n
            + Integral (IntegrableDiscrDeriv IS fn fnInt (S n))).
    2: reflexivity.
    rewrite IHn. clear IHn.
    pose proof (IntegralMinus (fn (S n)) (fn n)).
    unfold IntegrableDiscrDeriv. rewrite H.
    unfold CRminus. rewrite CRplus_comm, CRplus_assoc, CRplus_opp_l.
    rewrite CRplus_0_r. reflexivity.
Qed.

Lemma SumDiscrDerivIncrAbs
  : forall (IS : IntegrationSpace)
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n))
      (n : nat),
    (forall n:nat, partialFuncLe (fn n) (fn (S n)))
    -> CRsum (fun k : nat =>
      Integral (IntegrableAbs
                  (DiscrDeriv (X (ElemFunc IS)) fn k)
                  (IntegrableDiscrDeriv IS fn fnInt k))) n
      == match n with
        | O => Integral (IntegrableAbs (fn O) (fnInt O))
        | S p => (Integral (fnInt n)
                + Integral (IntegrableAbs (fn O) (fnInt O))
                  - Integral (fnInt O))
        end.
Proof.
  induction n.
  - reflexivity.
  - intros. specialize (IHn H). destruct n.
    + clear IHn. unfold CRsum, IntegrableDiscrDeriv, DiscrDeriv.
      unfold CRminus.
      rewrite <- (CRplus_comm (Integral (IntegrableAbs (fn 0%nat) (fnInt 0%nat)))).
      rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
      pose proof (@IntegralMinus IS). unfold CRminus in H0.
      rewrite <- H0. clear H0. apply IntegralExtensional.
      intros.
      rewrite applyXabs. rewrite CRabs_right.
      apply DomainProp. destruct xdf.
      rewrite (applyXminus (fn 1%nat) (fn O)).
      apply CRle_minus. apply H.
    + assert (forall f n, @CRsum (RealT (ElemFunc IS)) f (S (S n)) = CRsum f (S n) + (f (S (S n)))).
      { intros. simpl. reflexivity. }
      rewrite H0. rewrite IHn. clear IHn. clear H0.
      setoid_replace (Integral
        (IntegrableAbs (DiscrDeriv (X (ElemFunc IS)) fn (S (S n)))
                       (IntegrableDiscrDeriv IS fn fnInt (S (S n)))))
        with (Integral (fnInt (S (S n))) - Integral (fnInt (S n))).
      unfold CRminus.
      rewrite <- (CRplus_comm (Integral (fnInt (S (S n))) + - Integral (fnInt (S n)))).
      do 3 rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
      pose proof (@IntegralMinus IS).
      rewrite <- H0. clear H0.
      apply IntegralExtensional. intros.
      intros.
      rewrite applyXabs. rewrite CRabs_right.
      apply DomainProp.
      unfold DiscrDeriv. destruct xdf.
      rewrite (applyXminus (fn (S (S n))) (fn (S n))).
      apply CRle_minus. apply H.
Qed.

(* The converse is not true : it is harder for series to converge absolutely. *)
Lemma DiscrDerivInfiniteSum
  : forall {R : ConstructiveReals} (X : Set) (fn : nat -> @PartialFunction R X),
    PartialRestriction (XinfiniteSumAbs (DiscrDeriv X fn))
                       (XpointwiseLimit fn).
Proof.
  split.
  - intros x H. simpl. destruct H as [xn xcv].
    exists (DiscrDerivDomainIncReverse X fn x xn).
    (* An absolutely convergent series converges without the absolute values. *)
    assert (CR_cauchy _
              (CRsum
                     (fun n : nat => CRabs _ (partialApply (DiscrDeriv X fn n) x (xn n))))).
    { intro p. specialize (xcv p) as [n nmaj]. exists n.
      simpl. exact nmaj. }
    clear xcv. apply series_cv_abs in H. destruct H as [l xcv].
    apply (Rcv_cauchy_mod _ l).
    apply (CR_cv_eq
             _ (CRsum (fun n : nat => partialApply (DiscrDeriv X fn n) x (xn n)))).
    2: exact xcv. intro n. apply DiscrDerivApply.
  - intros. apply applyInfiniteSumAbs.
    destruct xG as [xn xcv].
    apply (CR_cv_eq _ (fun n : nat => partialApply (fn n) x (xn n))).
    intro n. symmetry. apply DiscrDerivApply.
    clear xD. simpl.
    destruct (CR_complete R (fun n : nat => partialApply (fn n) x (xn n)) xcv).
    exact c.
Qed.

(* Now the famous monotone convergence theorem for integrals.
   Unlike the classical Beppo Levi's formulation, this theorem
   requires a convergence, to avoid infinite integrals. Also,
   constructively the convergence of non-decreasing sequences
   is not automatic ; this theorem proves that the restriction
   to the domain of convergence does not lose integral mass. *)
Definition IntegralMonotoneConvergence
           (IS : IntegrationSpace)
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
           (fnInt : forall n:nat, IntegrableFunction (fn n))
           (a : CRcarrier (RealT (ElemFunc IS)))
  : (forall n:nat, partialFuncLe (fn n) (fn (S n)))
    -> CR_cv _ (fun n:nat => Integral (fnInt n)) a
    -> { limInt : IntegrableFunction (XpointwiseLimit fn)
      | Integral limInt == a }.
Proof.
  intros.
  destruct (IntegrableFunctionsComplete
              IS (DiscrDeriv (X (ElemFunc IS)) fn)
              (IntegrableDiscrDeriv IS fn fnInt)
              (a + (Integral (IntegrableAbs (fn 0%nat) (fnInt 0%nat))
                    - Integral (fnInt 0%nat)))).
  apply (CR_cv_eq _ (fun n => match n with
        | O => Integral (IntegrableAbs (fn O) (fnInt O))
        | S p => (Integral (fnInt n)
                 + Integral (IntegrableAbs (fn O) (fnInt O))
                 - Integral (fnInt O))
        end)).
  - intro n. symmetry. apply SumDiscrDerivIncrAbs. assumption.
  - apply (CR_cv_shift _ 1).
    apply (CR_cv_eq _ (fun n => (Integral (fnInt (n + 1)%nat)
          + (Integral (IntegrableAbs (fn 0%nat) (fnInt 0%nat))
             - Integral (fnInt 0%nat))))).
    intro n. rewrite plus_comm. simpl.
    unfold CRminus. rewrite CRplus_assoc. reflexivity.
    apply CR_cv_plus.
    apply (CR_cv_shift' (fun i : nat => Integral (fnInt i)) 1).
    apply H0. intros n. exists O. intros. unfold CRminus.
    simpl. rewrite CRplus_opp_r. rewrite CRabs_right.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRle_refl.
  - destruct p.
    assert (PartialRestriction (XinfiniteSumAbs (IntFn x))
                               (XpointwiseLimit fn)) as H1.
    { apply (PartialRestriction_trans _ _ _ _ p).
      apply DiscrDerivInfiniteSum. }
    exists (existT _ x H1).
    pose proof (IntegralCv x); simpl.
    apply (CR_cv_unique (fun n : nat => Integral (fnInt n))).
    2: apply H0. clear H0.
    apply (CR_cv_eq
             _ (CRsum (fun n : nat =>
                 Integral (IntegrableDiscrDeriv IS fn fnInt n)))).
    intro n. apply SumDiscrDeriv. apply s.
Qed.

Lemma SumDiscrDerivDecrAbs
  : forall (IS : IntegrationSpace)
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n))
      (n : nat),
    (forall n:nat, partialFuncLe (fn (S n)) (fn n))
    -> CRsum (fun k : nat => Integral (IntegrableAbs _ (IntegrableDiscrDeriv IS fn fnInt k))) n
      == match n with
        | O => Integral (IntegrableAbs (fn O) (fnInt O))
        | S p => (- Integral (fnInt n)
                 + Integral (IntegrableAbs (fn O) (fnInt O))
                 + Integral (fnInt O))
        end.
Proof.
  induction n.
  - reflexivity.
  - intros. specialize (IHn H). destruct n.
    + clear IHn. unfold CRsum, IntegrableDiscrDeriv, DiscrDeriv, CRminus.
      rewrite <- (CRplus_comm (Integral (IntegrableAbs (fn 0%nat) (fnInt 0%nat)))).
      rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
      pose proof (@IntegralMinus IS). unfold CRminus in H0.
      rewrite CRplus_comm.
      rewrite <- H0. clear H0. apply IntegralExtensional.
      intros.
      rewrite applyXabs. specialize (H O).
      destruct xdf, xdg.
      rewrite (applyXminus (fn 1%nat) (fn O)).
      rewrite (applyXminus (fn O) (fn 1%nat)).
      destruct (fn 1%nat), (fn O).
      rewrite (DomainProp x d2 d), (DomainProp0 x d1 d0).
      rewrite CRabs_minus_sym. simpl.
      rewrite CRabs_right. reflexivity.
      specialize (H x d d0); simpl in H.
      rewrite <- (CRplus_opp_r (partialApply x d)).
      apply CRplus_le_compat. exact H. apply CRle_refl.
    + assert (forall f n, @CRsum (RealT (ElemFunc IS)) f (S (S n)) = CRsum f (S n) + (f (S (S n)))).
      intros. simpl. reflexivity.
      rewrite H0. rewrite IHn. clear IHn. clear H0.
      setoid_replace (Integral
        (IntegrableAbs (DiscrDeriv (X (ElemFunc IS)) fn (S (S n)))
             (IntegrableDiscrDeriv IS fn fnInt (S (S n)))))
        with (Integral (fnInt (S n)) - Integral (fnInt (S (S n)))).
      rewrite <- (CRplus_comm (Integral (fnInt (S n)) - Integral (fnInt (S (S n))))).
      do 2 rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
      apply CRplus_morph. 2: reflexivity. rewrite CRplus_comm.
      unfold CRminus. rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      reflexivity. pose proof (@IntegralMinus IS).
      rewrite <- H0. clear H0.
      apply IntegralExtensional.
      intros. specialize (H (S n)).
      rewrite applyXabs. simpl in xdg.
      unfold DiscrDeriv. destruct xdf, xdg.
      rewrite (applyXminus (fn (S (S n))) (fn (S n))).
      rewrite (applyXminus (fn (S n)) (fn (S (S n)))).
      destruct (fn (S n)), (fn (S (S n))).
      rewrite (DomainProp0 x d2 d), (DomainProp x d1 d0).
      rewrite CRabs_minus_sym.
      rewrite CRabs_right. simpl. reflexivity.
      rewrite <- (CRplus_opp_r (partialApply0 x d)).
      apply CRplus_le_compat. apply H. apply CRle_refl.
Qed.

Definition IntegralMonotoneConvergenceDecr
           (IS : IntegrationSpace)
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
           (fnInt : forall n:nat, IntegrableFunction (fn n))
           (a : CRcarrier (RealT (ElemFunc IS)))
  : (forall n:nat, partialFuncLe (fn (S n)) (fn n))
    -> CR_cv _ (fun n:nat => Integral (fnInt n)) a
    -> { limInt : IntegrableFunction (XpointwiseLimit fn)
      | Integral limInt == a }.
Proof.
  intros.
  destruct (IntegrableFunctionsComplete
              IS (DiscrDeriv (X (ElemFunc IS)) fn)
              (IntegrableDiscrDeriv IS fn fnInt)
              (- a + (Integral (IntegrableAbs (fn 0%nat) (fnInt 0%nat))
                      + Integral (fnInt 0%nat)))).
  apply (CR_cv_eq _ (fun n => match n with
        | O => Integral (IntegrableAbs (fn O) (fnInt O))
        | S _ => (- Integral (fnInt n)
                 + Integral (IntegrableAbs (fn O) (fnInt O))
                 + Integral (fnInt O))
        end)).
  - intro n. symmetry. apply SumDiscrDerivDecrAbs. assumption.
  - apply (CR_cv_shift _ 1).
    apply (CR_cv_eq _ (fun n => (- Integral (fnInt (n + 1)%nat)
                              + (Integral (IntegrableAbs (fn 0%nat) (fnInt 0%nat))
                                 + Integral (fnInt 0%nat))))).
    intro n. rewrite plus_comm. simpl.
    rewrite CRplus_assoc. reflexivity.
    apply CR_cv_plus. apply CR_cv_opp.
    apply (CR_cv_shift' (fun i : nat => Integral (fnInt i)) 1).
    apply H0. intros n. exists O. intros. unfold CRminus.
    simpl. rewrite CRplus_opp_r. rewrite CRabs_right.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRle_refl.
  - destruct p.
    assert (PartialRestriction (XinfiniteSumAbs (IntFn x))
                               (XpointwiseLimit fn)) as H1.
    { apply (PartialRestriction_trans _ _ _ _ p).
      apply DiscrDerivInfiniteSum. }
    exists (existT _ x H1).
    pose proof (IntegralCv x); simpl.
    apply (CR_cv_unique (fun n : nat => Integral (fnInt n))).
    2: apply H0. clear H0.
    apply (CR_cv_eq _ (CRsum (fun n : nat =>
           Integral (IntegrableDiscrDeriv IS fn fnInt n)))).
    intro n. apply SumDiscrDeriv. apply s.
Qed.

Definition IntegralRepresentationShift
           {IS : IntegrationSpace}
           (fInt : @IntegralRepresentation IS) (n : nat) : @IntegralRepresentation IS.
Proof.
  apply (Build_IntegralRepresentation
           IS (fun k => IntFn fInt (S n + k))
           (fun k => IntFnL fInt (S n + k))
           (IntAbsSum fInt - CRsum (fun k => Iabs _ (IntFnL fInt k)) n)).
  apply (CR_cv_eq _ (fun i => CRsum (fun k : nat => Iabs _ (IntFnL fInt k)) (S n+i)
                               - CRsum (fun k : nat => Iabs _ (IntFnL fInt k)) n)).
  intros i. rewrite sum_assoc. simpl.
  unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
  rewrite CRplus_0_l. reflexivity.
  apply CR_cv_plus. 2: apply CR_cv_const.
  intro p. destruct fInt; unfold CMTIntegrableFunctions.IntFn,
                          CMTIntegrableFunctions.IntAbsSum,
                          CMTIntegrableFunctions.IntFnL.
  specialize (IntAbsSumCv p) as [j jmaj].
  exists j. intros. apply jmaj.
  apply (le_trans _ (0+i) _ H). apply Nat.add_le_mono_r, le_0_n.
Defined.

Lemma IntegralRepresentationShiftVal
  : forall {IS : IntegrationSpace}
      (fInt : @IntegralRepresentation IS) (n : nat),
    IntegralSeries (IntegralRepresentationShift fInt n)
    == IntegralSeries fInt - CRsum (fun k => I IS _ (IntFnL fInt k)) n.
Proof.
  intros.
  apply (series_cv_unique (fun n0 : nat =>
         I IS (IntFn (IntegralRepresentationShift fInt n) n0)
           (IntFnL (IntegralRepresentationShift fInt n) n0))).
  exact (IntegralCv (IntegralRepresentationShift fInt n)).
  simpl.
  apply (CR_cv_eq
           _ (fun k => CRsum (fun n0 : nat => I IS _ (IntFnL fInt n0)) (S n + k)
                    - CRsum (fun k : nat => I IS (IntFn fInt k) (IntFnL fInt k)) n)).
  intros. rewrite sum_assoc. simpl.
  unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
  reflexivity.
  apply CR_cv_minus. 2: apply CR_cv_const.
  intro p.
  pose proof (IntegralCv fInt p) as [k kmaj]. exists k.
  intros. apply kmaj. apply (le_trans _ (0+i) _ H).
  apply Nat.add_le_mono_r, le_0_n.
Qed.


(* The integrable functions were defined as pointwise limits of L-functions,
   which is already a notion of density. Here we prove that integrable functions
   are also limits for the integral distance.
   This is corollary 1.17 of Bishop. *)
Lemma IntegralDense : forall {IS : IntegrationSpace}
                        (f : PartialFunction (X (ElemFunc IS)))
                        (fInt : IntegrableFunction f),
    Un_integral_cv _ f
                   (IntegrableSum _ (fun n => IntegrableL _ (IntFnL (let (intRepres,_) := fInt in intRepres) n)))
                   fInt.
Proof.
  intros. destruct fInt as [intRepres lim]. intro p.
  pose proof (IntAbsSumCv intRepres p) as [n nmaj]. exists n.
  intros.
  apply (CRle_trans
           _ (Integral (IntegrableSelf (IntegralRepresentationShift
                                          (IntegralRepresentationAbs intRepres) n)))).
  - apply IntegralNonDecreasing.
    intros x xdf [xnlim cau]. destruct xdf.
    rewrite applyXabs, (applyXminus (Xsum (IntFn intRepres) n) f).
    simpl.
    assert (forall n0:nat, Domain (IntFn intRepres  n0) x) as xdn.
    { intro j. destruct (le_lt_dec j n).
      apply (domainXsumIncReverse (IntFn intRepres) j n).
      exact d. exact l. unfold lt in l. simpl in xnlim.
      pose proof (xnlim (j - S n)%nat) as H0.
      replace (S (n + (j - S n)))%nat with j in H0. exact H0.
      symmetry. exact (le_plus_minus_r (S n) j l). }
    destruct (series_cv_abs (fun n0 : nat => CRabs _ (partialApply (IntFn intRepres (S (n + n0))) x (xnlim n0)))
                            cau) as [x0 s].
    apply (series_cv_eq
             _ (fun n0 => CRabs _ (partialApply (IntFn intRepres (S (n + n0))) x (xdn (S n + n0)%nat)))) in s.
    apply (series_cv_shift (fun n0 : nat =>
                              CRabs _ (partialApply (IntFn intRepres n0) x (xdn n0))) n x0) in s.
    rewrite (applyXsum _ _ x _ xdn).
    rewrite <- (CRplus_0_r x0),
    <- (CRplus_opp_r
          (CRsum (fun n0 : nat => CRabs _ (partialApply (IntFn intRepres n0) x (xdn n0))) n)),
    <- CRplus_assoc.
    apply (series_cv_abs_remainder
             (fun n0 : nat => (partialApply (IntFn intRepres n0) x (xdn n0)))
             (partialApply f x d0)
             (x0 +
              CRsum
                (fun n0 : nat =>
                   CRabs _ (partialApply (IntFn intRepres n0) x (xdn n0))) n) n).
    2: exact s.
    destruct lim.
    assert (Domain (XinfiniteSumAbs (IntFn intRepres)) x) as H0.
    { exists xdn. apply Rcv_cauchy_mod in s. exact s. }
    rewrite <- (c x H0).
    apply (series_cv_eq (fun n : nat =>
                           partialApply (IntFn intRepres n) x
                                        (domainInfiniteSumAbsIncReverse (IntFn intRepres) x H0 n))).
    2: apply applyInfiniteSumAbs; reflexivity.
    intros. apply DomainProp.
    intros. apply CRabs_morph, DomainProp.
  - unfold Integral, IntegrableSelf.
    rewrite IntegralRepresentationShiftVal.
    rewrite IntegralRepresentationAbsVal. simpl.
    specialize (nmaj n (le_refl n)). rewrite CRabs_minus_sym in nmaj.
    apply (CRle_trans _ _ _ (CRle_abs _) nmaj).
Qed.

Lemma CR_cv_growing : forall {R : ConstructiveReals}
                        (un : nat -> CRcarrier R) (l : CRcarrier R),
    (forall n:nat, un n <= un (S n))
    -> (forall n:nat, un n <= l)
    -> (forall p : positive, { n : nat  |  l - un n <= CR_of_Q R (1#p) })
    -> CR_cv R un l.
Proof.
  intros. intro p.
  specialize (H1 p) as [n nmaj]. exists n.
  intros. rewrite CRabs_minus_sym, CRabs_right.
  apply (CRle_trans _ (l - un n)). apply CRplus_le_compat_l.
  apply CRopp_ge_le_contravar.
  exact (growing_transit _ H n i H1). exact nmaj.
  rewrite <- (CRplus_opp_r (un i)). apply CRplus_le_compat.
  apply H0. apply CRle_refl.
Qed.

Lemma IntegralTruncateLimit
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
    CR_cv _
      (fun n : nat => Integral (IntegrableMinInt f n fInt))
      (Integral fInt).
Proof.
  (* Fallback to the L-version of this theorem via
     the L-representation fn of f. *)
  intros IS f fInt. apply CR_cv_growing.
  - intro n. apply IntegralNonDecreasing.
    intros x xdf xdg.
    assert (Domain f x).
    { destruct f; exact xdf. }
    apply CRmin_glb.
    unfold XminConst, Xop, partialApply.
    rewrite (DomainProp f x xdf xdg). apply CRmin_l.
    apply (CRle_trans _ _ _ (CRmin_r _ _)).
    apply CR_of_Q_le.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
    apply Nat2Z.inj_le, le_S, le_refl.
  - intro n. apply IntegralNonDecreasing.
    intros x xdf xdg. unfold XminConst, Xop, partialApply.
    rewrite (DomainProp f x xdf xdg). apply CRmin_l.
  - intro p.
    assert ({ g : PartialFunction (X (ElemFunc IS))
                  & { gL : L (ElemFunc IS) g
                    | IntegralDistance f g fInt (IntegrableL g gL) <= CR_of_Q _ (1#3*p) } }).
    { pose proof (IntegralDense f fInt (3*p)%positive) as [n nmaj].
      specialize (nmaj n (le_refl n)).
      exists (Xsum (IntFn (let (intRepres, _) := fInt in intRepres)) n).
      exists (LsumStable _ (IntFnL (let (intRepres, _) := fInt in intRepres)) n).
      rewrite IntegralDistance_sym.
      apply (CRle_trans _ (IntegralDistance (Xsum (IntFn (let (intRepres, _) := fInt in intRepres)) n) f
           (IntegrableSum (IntFn (let (intRepres, _) := fInt in intRepres))
              (fun n : nat =>
               IntegrableL (IntFn (let (intRepres, _) := fInt in intRepres) n)
                 (IntFnL (let (intRepres, _) := fInt in intRepres) n)) n) fInt)).
      2: exact nmaj. clear nmaj.
      apply IntegralNonDecreasing. intros x xdf xdg.
      rewrite (DomainProp _ _ xdf xdg). apply CRle_refl. }
    destruct X as [g [gL gdist]].
    pose proof (Ilimit IS g gL) as [glim _].
    specialize (glim (3*p)%positive) as [n nmaj]. exists n.
    apply (CRle_trans
             _ (I IS g gL + CR_of_Q _ (1#3*p)
                 - Integral (IntegrableMinInt f n fInt))).
    apply CRplus_le_compat. 2: apply CRle_refl.
    apply (CRplus_le_reg_l (-I IS g gL)).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    rewrite CRplus_comm.
    apply (CRle_trans _ _ _ (CRle_abs _)).
    fold (Integral fInt - I IS g gL).
    rewrite <- IntegralLstable. rewrite <- IntegralMinus.
    exact (CRle_trans _ _ _ (IntegralTriangle _ _) gdist).
    apply (CRle_trans _ (I IS g gL + CR_of_Q _ (1 # 3 * p)
                                     - I IS _ (LminIntStable n g gL)
                         + CR_of_Q _ (1#3*p))).
    unfold CRminus. rewrite (CRplus_assoc (I IS g gL + CR_of_Q _ (1 # 3 * p))).
    apply CRplus_le_compat. apply CRle_refl.
    apply (CRplus_le_reg_l (I IS _ (LminIntStable n g gL))).
    rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    fold (I IS _ (LminIntStable n g gL)
          - Integral (IntegrableMinInt f n fInt)).
    rewrite <- IntegralLstable, <- IntegralMinus.
    apply (CRle_trans _ _ _ (CRle_abs _)).
    apply (CRle_trans _ _ _ (IntegralTriangle _ _)).
    apply (CRle_trans _ (IntegralDistance f g fInt (IntegrableL g gL))).
    2: exact gdist. rewrite IntegralDistance_sym.
    apply IntegralNonDecreasing. intros x xdf xdg. destruct xdf, xdg.
    rewrite applyXabs, applyXabs,
    (applyXminus (XminConst g (INR n)) (XminConst f (INR n))),
    (applyXminus g f), applyXminConst, applyXminConst.
    assert (0 <= @INR (RealT (ElemFunc IS)) n) as nPos.
    { rewrite <- CR_of_Q_zero. apply CR_of_Q_le. unfold Qle, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. apply Nat2Z.is_nonneg. }
    apply (CRle_trans _ _ _ (CRmin_contract _ _ _)).
    rewrite (DomainProp g x d d1).
    rewrite (DomainProp f x d0 d2).
    apply CRle_refl.
    apply (CRle_trans
             _ (CR_of_Q _ (1 # 3 * p) + CR_of_Q _ (1 # 3 * p) + CR_of_Q _ (1 # 3 * p))).
    apply CRplus_le_compat. 2: apply CRle_refl.
    unfold CRminus. rewrite (CRplus_comm (I IS g gL)), CRplus_assoc.
    apply CRplus_le_compat_l.
    specialize (nmaj n (le_refl n)). rewrite CRabs_minus_sym in nmaj.
    exact (CRle_trans _ _ _ (CRle_abs _) nmaj).
    rewrite <- CR_of_Q_plus, <- CR_of_Q_plus. apply CR_of_Q_le.
    rewrite Qinv_plus_distr, Qinv_plus_distr.
    unfold Qle, Qnum, Qden. rewrite Z.mul_1_l.
    rewrite Pos2Z.inj_mul. reflexivity.
Qed.



Lemma Break_lt_3_eps :
  forall {R : ConstructiveReals} (a b : CRcarrier R),
    a < b
    -> { eps : CRcarrier R
              & prod (0 < eps) (a + CR_of_Q R 3 * eps < b) }.
Proof.
  intros. exists ((b-a) * CR_of_Q R (1#4)). split.
  - rewrite <- (CRmult_0_l (CR_of_Q R (1#4))).
    apply CRmult_lt_compat_r. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    rewrite <- (CRplus_opp_r a). apply CRplus_lt_compat_r. exact H.
  - rewrite (CRmult_comm (b-a)), <- CRmult_assoc, <- CR_of_Q_mult.
    apply (CRplus_lt_reg_l _ (-a)). rewrite <- CRplus_assoc.
    rewrite CRplus_opp_l, CRplus_0_l, (CRplus_comm (-a)).
    rewrite <- (CRmult_1_l (b + - a)).
    apply CRmult_lt_compat_r.
    rewrite <- (CRplus_opp_r a). apply CRplus_lt_compat_r. exact H.
    rewrite <- CR_of_Q_one. apply CR_of_Q_lt. reflexivity.
Qed.

Lemma DiagNonNeg
  : forall {R : ConstructiveReals} {X : Set}
           (fnk : nat -> nat -> @PartialFunction R X),
    (forall n k:nat, nonNegFunc (fnk n k))
    -> forall n:nat, nonNegFunc (diagSeq fnk n).
Proof.
  intros. intros x xdf. unfold diagSeq. unfold diagSeq in xdf.
  destruct (diagPlaneInv n). apply H.
Qed.

Lemma applyDiagAbs
  : forall {R : ConstructiveReals} {X : Set} (fnk : nat -> nat -> PartialFunction X)
      (x : X)
      (cpxDdiag : forall k : nat,
             Domain
               (diagSeq (fun n k0 : nat => Xabs (fnk n k0)) k) x)
      (cpxDdiagBis : forall k : nat,
          Domain (diagSeq fnk k) x)
      (k : nat),
    partialApply _ x (cpxDdiag k)
    == CRabs R (partialApply _ x (cpxDdiagBis k)).
Proof.
  intros. unfold diagSeq.
  generalize (cpxDdiag k). intro d. generalize (cpxDdiagBis k). intro d0.
  clear cpxDdiagBis cpxDdiag. unfold diagSeq in d, d0.
  destruct (diagPlaneInv k).
  apply CRabs_morph. apply DomainProp.
Qed.

Definition series_cv_two_lim_lt
           {R : ConstructiveReals} (un vn : nat -> CRcarrier R) (a : CRcarrier R) : Set
  := { xy : CRcarrier R * CRcarrier R & (series_cv un (fst xy))
                            * (series_cv vn (snd xy))
                            * (fst xy + snd xy < a)%ConstructiveReals }%type.

Record CommonPointFunTwoSeq {R : ConstructiveReals} {X : Set}
       {f : @PartialFunction R X}
       {fn : nat -> @PartialFunction R X}
       {gn : nat -> @PartialFunction R X} : Set
  := {
      cpx2 : X;
      cpxF2 : Domain f cpx2;
      cpxFn2 : forall n:nat, Domain (fn n) cpx2;
      cpxGn2 : forall n:nat, Domain (gn n) cpx2;
    }.

(* Icontinuous with 2 approching sequences, instead of 1. *)
Lemma IcontinuousWeave
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (gn : nat -> PartialFunction (X (ElemFunc IS)))
      (fL : (L (ElemFunc IS)) f)
      (fnL : forall n:nat, (L (ElemFunc IS)) (fn n))
      (gnL : forall n:nat, (L (ElemFunc IS)) (gn n)),
    (forall n:nat, nonNegFunc (fn n))
    -> (forall n:nat, nonNegFunc (gn n))
    -> series_cv_two_lim_lt (fun n => I IS (fn n) (fnL n))
                           (fun n => I IS (gn n) (gnL n))
                           (I IS f fL)
    -> { x : @CommonPointFunTwoSeq _ _ f fn gn
            & series_cv_two_lim_lt (fun n => partialApply (fn n) _ (cpxFn2 x n))
                                   (fun n => partialApply (gn n) _ (cpxGn2 x n))
                                   (partialApply f _ (cpxF2 x)) }.
Proof.
  intros.
  assert (forall n:nat, L (ElemFunc IS) (weaveSequences _ fn gn n)) as wL.
  { apply weaveSequencesL; assumption. }
  destruct (Icontinuous IS f
                        (weaveSequences _ fn gn)
                        fL wL).
  - intro n. unfold weaveSequences.
    destruct (Nat.even n). apply H. apply H0.
  - destruct H1, x. simpl in p. destruct p, p.
    exists (c+c0). split. 2: exact c1.
    apply (series_cv_eq
             (weaveSequences _
                (fun n => I IS (fn n) (fnL n))
                (fun n => I IS (gn n) (gnL n)))).
    intro n. unfold weaveSequences.
    generalize (wL n). intros. unfold weaveSequences in l.
    destruct (Nat.even n).
    apply IExtensional. intros. apply DomainProp.
    apply IExtensional. intros. apply DomainProp.
    apply weaveInfiniteSums; assumption.
  - destruct x; simpl in s. destruct s, p.
    assert (forall k:nat, Domain (fn k) cpx) as cpxDf.
    { intro k. exact (domainWeaveEvenInc _ _ _ k cpx (cpxFn (k*2)%nat)). }
    assert (forall k:nat, Domain (gn k) cpx) as cpxDg.
    { intro k. exact (domainWeaveOddInc _ _ _ k cpx (cpxFn (1+k*2)%nat)). }
    apply (series_cv_eq
             _ (weaveSequences
                  _
                  (fun n => partialApply _ cpx (cpxDf n))
                  (fun n => partialApply _ cpx (cpxDg n))))
      in s.

    assert ({ l : CRcarrier _
                  & series_cv (fun n => partialApply _ cpx (cpxDg n)) l}).
    { apply (halfWeavedSumOdd
               (fun n => partialApply _ cpx (cpxDf n)) _ x).
      intro k. apply H.
      intro k. apply H0. exact s. }
    destruct H2.
    assert ({ l : CRcarrier _
                  & series_cv (fun k => partialApply _ cpx (cpxDf k)) l}).
    { apply (halfWeavedSumEven
               _ (fun k => partialApply _ cpx (cpxDg k)) x).
      intro k. apply H.
      intro k. apply H0. exact s. }
    destruct H2.
    exists (Build_CommonPointFunTwoSeq _
         _ _ _ _ cpx cpxF cpxDf cpxDg). simpl.
    exists (x1,x0). split. split. exact s1. exact s0. simpl.
    setoid_replace (x1+x0) with x. exact c.
    apply (series_cv_unique
             (weaveSequences _ (fun n : nat => partialApply (fn n) cpx (cpxDf n))
                             (fun n : nat => partialApply (gn n) cpx (cpxDg n)))).
    2: exact s.
    apply weaveInfiniteSums; assumption.
    intro k.
    rewrite (partialApplyWeave
               _ fn gn
               k cpx (cpxDf (k/2)%nat) (cpxDg (k/2)%nat) (cpxFn k)).
    unfold weaveSequences. destruct (Nat.even k); reflexivity.
Qed.

Lemma series_cv_remainder_cv
  : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (l eps : CRcarrier R),
    series_cv un l
    -> 0 < eps
    -> { k : nat & forall i:nat, le k i -> series_cv_lim_lt (fun n => un (n + i)%nat) eps }.
Proof.
  intros.
  destruct (Un_cv_nat_real (CRsum un) l H eps H0) as [k kmaj].
  exists (S k). intros.
  pose proof (series_cv_shift' un l i H).
  destruct i. exfalso; inversion H1.
  exists (l - CRsum un i). split. exact H2.
  apply le_S_n in H1. specialize (kmaj i H1).
  rewrite CRabs_minus_sym in kmaj.
  exact (CRle_lt_trans _ _ _ (CRle_abs _) kmaj).
Qed.

(* The completed space of integrable function is an integration space. *)
Lemma IntegrableContinuous
  : forall {IS : IntegrationSpace}
      (h : PartialFunction (X (ElemFunc IS)))
      (hn : nat -> PartialFunction (X (ElemFunc IS)))
      (hL : IntegrableFunction h)
      (hnL : forall n:nat, IntegrableFunction (hn n)),
    (forall n:nat, nonNegFunc (hn n))
    -> series_cv_lim_lt (fun n => Integral (hnL n)) (Integral hL)
    -> { x : CommonPointFunSeq _ h hn
            & series_cv_lim_lt (fun n => partialApply (hn n) _ (cpxFn _ _ _ x n))
                               (partialApply h _ (cpxF _ _ _ x)) }.
Proof.
  intros. destruct H0, p.
  destruct (Break_lt_3_eps _ _ c) as [eps [epsPos epsMaj]].
  assert (forall n:nat, 0 < eps * CR_of_Q _ (1#2) * CRpow (CR_of_Q _ (1#2)) n).
  { intro n. rewrite <- (CRmult_0_r eps).
    rewrite CRmult_assoc.
    apply CRmult_lt_compat_l. exact epsPos.
    rewrite <- (CRmult_0_r (CR_of_Q _ (1#2))).
    apply CRmult_lt_compat_l. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    apply pow_lt. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. }
  pose (fun n => IntFn (let (r,_)
                         := AbsRepresentation
                              IS (hn n) (eps*CR_of_Q _ (1#2)*CRpow (CR_of_Q _ (1#2)) n)
                              (hnL n) (H0 n) in r))
    as phink.
  pose ( fun n k : nat =>
   let s1 :=
       AbsRepresentation IS (hn n) (eps * CR_of_Q _ (1#2) * CRpow (CR_of_Q _ (1 # 2)) n)
                         (hnL n) (H0 n) in
   let (x0, _) as s2 return (L (ElemFunc IS) (IntFn (let (r, _) := s2 in r) k)) :=
     s1 in
   let X := IntFnL x0 in X k) as phinkL.
  assert (forall n:nat, { l : CRcarrier _
                       & (series_cv (fun k => I IS (Xabs (phink n k))
                                             (LabsStable _ _ (phinkL n k))) l)
                         * (l <= Integral (hnL n) + eps * CR_of_Q _ (1#2)* CRpow (CR_of_Q _ (1#2)) n)%ConstructiveReals }%type)
    as phinkAbsCv.
  { intro n. unfold phink, phinkL.
    destruct (AbsRepresentation IS (hn n) (eps * CR_of_Q _ (1#2) * CRpow (CR_of_Q _ (1 # 2)) n)
                                (hnL n) (H0 n)).
    exists (IntAbsSum x0). split. exact (IntAbsSumCv x0). destruct p.
    setoid_replace (Integral (hnL n))
      with (Integral (IntegrableAbs (hn n) (hnL n))). exact c0.
    apply IntegralExtensional. intros. simpl.
    rewrite CRabs_right. apply DomainProp. apply H. }
  assert (forall n:nat, PartialRestriction (XinfiniteSumAbs (phink n)) (hn n)) as phinkRes.
  { intros n. unfold phink.
    destruct (AbsRepresentation
                IS (hn n) (eps * CR_of_Q _ (1#2)*CRpow (CR_of_Q _ (1 # 2)) n) (hnL n) (H0 n)).
    apply p. }
  destruct hL as [x0 psiRes], x0 as [psik psikL IntAbsSum IntAbsSumCv].
  unfold Integral in epsMaj, c. unfold IntFn in psiRes.
  assert (CR_cv _ (fun K => I IS (Xsum psik K) (LsumStable psik psikL K))
                 (IntegralSeries {|
         IntFn := psik;
         IntFnL := psikL;
         IntAbsSum := IntAbsSum;
         IntAbsSumCv := IntAbsSumCv |})) as psiInt.
  { apply (CR_cv_eq _ (CRsum (fun K => I IS (psik K) (psikL K)))).
    intro n. rewrite IadditiveIterate. reflexivity.
    unfold IntegralSeries.
    destruct (
       series_cv_maj (fun n : nat => I IS (psik n) (psikL n))
         (fun k : nat => Iabs (psik k) (psikL k)) IntAbsSum
         (fun n : nat => integralAbsMaj (psik n) (psikL n)) IntAbsSumCv).
    destruct p. exact s0. }
  assert ({K : nat & prod (IntegralSeries {|
         IntFn := psik;
         IntFnL := psikL;
         IntAbsSum := IntAbsSum;
         IntAbsSumCv := IntAbsSumCv |}
                         < I IS (Xsum psik K) (LsumStable psik psikL K) + eps)
                        (series_cv_lim_lt (fun k => I IS (Xabs (psik (k+S K)%nat))
                                                   (LabsStable _ _ (psikL _)))
                                          eps) }).
  { pose proof (Un_cv_nat_real _ _  psiInt eps epsPos) as [i imaj].
    destruct (series_cv_remainder_cv
                _ _ eps IntAbsSumCv epsPos) as [j jmaj].
    exists (max i j). split.
    specialize (imaj (max i j) (Nat.le_max_l _ _)).
    rewrite CRabs_minus_sym in imaj.
    apply (CRplus_lt_reg_l _
             (- I IS (Xsum psik (Init.Nat.max i j)) (LsumStable psik psikL (Init.Nat.max i j)))).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_comm.
    apply (CRle_lt_trans _ _ _ (CRle_abs _)). exact imaj.
    apply jmaj. apply le_S, Nat.le_max_r. }
  destruct H1 as [K kmaj].
  assert (forall n:nat, L (ElemFunc IS) (diagSeq (fun n k => Xabs (phink n k)) n)) as L1.
  { apply diagSeqL. intros n k. apply LabsStable. apply phinkL. }
  assert (forall k:nat, L (ElemFunc IS) (Xabs (psik (k+S K)%nat))) as L2.
  { intro k. apply LabsStable. apply psikL. }
  destruct (IcontinuousWeave
              (Xsum psik K)
              (diagSeq (fun n k => Xabs (phink n k)))
              (fun k => Xabs (psik (k+S K)%nat))
              (LsumStable psik psikL K) L1 L2)
    as [x0 xcv].
  - intro n.
    unfold diagSeq. destruct (diagPlaneInv n).
    intros y ydf. apply CRabs_pos.
  - intros n y ydf. apply CRabs_pos.
  - destruct kmaj, s0, p.
    destruct (series_cv_maj
                (fun n => let (l,_):=phinkAbsCv n in l)
                (fun n => Integral (hnL n) + eps * CR_of_Q _ (1#2) * CRpow (CR_of_Q _ (1 # 2)) n)
                (x + eps)).
    intro n. destruct (phinkAbsCv n). simpl. destruct p.
    rewrite CRabs_right. exact c2.
    apply (series_cv_nonneg
             (fun k : nat => I IS (Xabs (phink n k))
            (LabsStable _ _ (phinkL n k)))).
    intros. apply integralPositive. intros y ydf. apply CRabs_pos.
    exact s1. apply series_cv_plus. exact s.
    apply (series_cv_eq
             (fun n : nat => CRpow (CR_of_Q _ (1 # 2)) n * (eps*CR_of_Q _ (1#2)))).
    intro n. apply CRmult_comm.
    apply (CR_cv_proper _ (CR_of_Q _ 2*(eps*CR_of_Q _ (1#2)))).
    apply series_cv_scale. apply GeoHalfTwo.
    rewrite CRmult_comm, CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1#2) * 2)%Q with 1%Q. rewrite CR_of_Q_one, CRmult_1_r.
    reflexivity. reflexivity. destruct p.
    exists (x1, x0). unfold fst, snd. split. split.
    apply (series_cv_eq
             (diagSeq (fun n k : nat => I IS (Xabs (phink n k))
                                     (LabsStable _ _ (phinkL n k))))).
    intro n. unfold diagSeq. generalize (L1 n). intros.
    unfold diagSeq in l. destruct (diagPlaneInv n).
    apply IExtensional. intros. apply DomainProp.
    apply (DiagSeqInfiniteSumColPos
             _ (fun n : nat => let (l, _) := phinkAbsCv n in l)).
    intros n k. apply integralPositive. intros y ydf. apply CRabs_pos.
    intro n. destruct (phinkAbsCv n). apply p.
    exact s1.
    apply (series_cv_eq
             (fun k : nat =>
          I IS (Xabs (psik (k + S K)%nat))
            (LabsStable (ElemFunc IS) (psik (k + S K)%nat) (psikL (k + S K)%nat)))).
    intro n. apply IExtensional. intros. apply DomainProp.
    exact s0.
    apply (CRplus_le_compat_l (eps+eps)) in c2.
    do 2 rewrite (CRplus_comm (eps+eps)) in c2.
    rewrite CRplus_assoc in c2.
    setoid_replace (eps + (eps+eps)) with (CR_of_Q _ 3 * eps) in c2.
    pose proof (CRle_lt_trans _ _ _ c2 epsMaj). clear c2.
    pose proof (CRlt_trans _ _ _ H1 c0). clear H1.
    rewrite <- CRplus_assoc in H2. apply CRplus_lt_reg_r in H2.
    apply (CRlt_trans _ (x1 + eps)).
    apply CRplus_lt_compat_l. exact c1. exact H2.
    setoid_replace (CR_of_Q (RealT (ElemFunc IS)) 3) with (1+1+CRone (RealT (ElemFunc IS))).
    do 2 rewrite CRmult_plus_distr_r. rewrite CRmult_1_l, CRplus_assoc.
    reflexivity. rewrite <- CR_of_Q_one.
    do 2 rewrite <- CR_of_Q_plus. reflexivity.
  - destruct x0 as [cpx cpxF cpxFn cpxGn].
    simpl in xcv. destruct xcv, p, x0. simpl in p. destruct p.
    simpl in c0.
    (* Prove that cpx is in Domain h,
       because it is in Domain (XinfinitesumAbs psik) *)
    assert (forall k:nat, Domain (psik k) cpx) as cpxDpsik.
    { intro k. destruct (le_lt_dec k K).
      apply (domainXsumIncReverse _ _ K). exact cpxF. exact l.
      rewrite <- (Nat.sub_add (S K) k).
      apply cpxGn. exact l. }
    assert (forall k:nat, Domain (diagSeq phink k) cpx) as cpxDdiagBis.
    { intro k. unfold diagSeq. destruct (diagPlaneInv k).
      apply (diagSeqDomain _ (fun n k => Xabs (phink n k)) _ cpxFn). }

    assert (Domain (XinfiniteSumAbs psik) cpx).
    { exists cpxDpsik.
      apply (Rcv_cauchy_mod
               _ (c2 + CRsum (fun k => partialApply
                                         (Xabs (psik k)) cpx (cpxDpsik k)) K)).
      apply series_cv_shift.
      apply (series_cv_eq
               (fun n : nat => CRabs _ (partialApply (psik (n + S K)%nat) cpx (cpxGn n)))).
      intros. apply CRabs_morph.
      rewrite (Nat.add_comm (S K)). apply DomainProp. exact s1. }
    assert (forall n:nat, Domain (XinfiniteSumAbs (phink n)) cpx).
    { intro n.
      apply (domainInfiniteSumAbsDiag
               _ (fun n0 k : nat => phink n0 k) n).
      exists cpxDdiagBis. apply (Rcv_cauchy_mod _ c1).
      apply (series_cv_eq
               (fun n : nat =>
          partialApply
            (diagSeq
               (fun n0 k : nat => Xabs (phink n0 k)) n) cpx
            (cpxFn n))).
      2: exact s0. apply applyDiagAbs. }
    assert (forall n:nat, Domain (hn n) cpx) as cpxDhn.
    { intro n. apply phinkRes. apply H2. }
    destruct psiRes.
    exists (Build_CommonPointFunSeq _ _ _ _ cpx (d _ H1) cpxDhn).
    simpl.
    assert ({ l : CRcarrier _
                  & prod (series_cv (fun n => partialApply _ cpx (cpxDhn n)) l)
                         (l <= c1) }).
    { destruct (DiagSeqInfiniteSum
                  (fun n k => partialApply (phink n k) cpx
                                        (diagSeqDomain _ phink cpx cpxDdiagBis n k))
                  (fun n => partialApply (hn n) cpx (cpxDhn n)) c1).
      apply (series_cv_eq
               (fun n : nat =>
                  partialApply
                    (diagSeq (fun n0 k : nat => Xabs (phink n0 k)) n) cpx
                    (cpxFn n))).
      intro n. rewrite (applyDiagAbs phink cpx cpxFn cpxDdiagBis).
      unfold diagSeq. generalize (cpxDdiagBis n).
      intros. unfold diagSeq in d0. destruct (diagPlaneInv n).
      apply CRabs_morph. apply DomainProp.
      exact s0. intro n.
      apply (series_cv_eq
               (fun k => partialApply (phink n k) cpx
                                   (domainInfiniteSumAbsIncReverse
                                      (phink n) cpx (H2 n) k))).
      intro i. apply DomainProp. apply applyInfiniteSumAbs.
      apply phinkRes.
      exists x0. split; apply p. }
    destruct H3, p.
    assert ({ l : CRcarrier _
                  & prod (series_cv (fun n => partialApply _ cpx (cpxDpsik (n+S K)%nat)) l)
                         (CRabs _ l <= c2) }).
    { destruct (series_cv_abs
                 (fun n => partialApply _ cpx (cpxDpsik (n+S K)%nat))).
      apply (Rcv_cauchy_mod _ c2).
      apply (series_cv_eq
               (fun n : nat => CRabs _ (partialApply (psik (n + S K)%nat) cpx (cpxGn n)))).
      intro n. apply CRabs_morph. apply DomainProp.
      exact s1.
      exists x1. split. exact s3.
      apply (series_cv_triangle
               (fun n => partialApply _ cpx (cpxDpsik (n+S K)%nat))).
      exact s3.
      apply (series_cv_eq
               (fun n : nat => CRabs _ (partialApply (psik (n + S K)%nat) cpx (cpxGn n)))).
      intro n. apply CRabs_morph. apply DomainProp. exact s1. }
    destruct H3.
    assert (x0 - x1 < partialApply (Xsum psik K) cpx cpxF).
    { apply (CRle_lt_trans _ (c1 + c2)).
      2: exact c0. apply CRplus_le_compat. exact c4.
      apply (CRle_trans _ (CRabs _ x1)).
      rewrite <- CRabs_opp. apply CRle_abs. apply p. }
    destruct p.
    clear c1 s0 c0 c4. clear c2 s1 c5.
    apply (CRplus_lt_compat_r x1) in H3.
    unfold CRminus in H3.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r in H3.
    exists x0. split. exact s2.
    rewrite (applyXsum _ K cpx _ cpxDpsik), CRplus_comm in H3.
    rewrite <- (c3 cpx H1).
    setoid_replace (partialApply (XinfiniteSumAbs psik) cpx H1)
      with (x1 + CRsum (fun k : nat => partialApply (psik k) cpx (cpxDpsik k)) K).
    exact H3. apply applyInfiniteSumAbs.
    apply (series_cv_eq (fun n : nat => partialApply (psik n) cpx (cpxDpsik n))).
    intro n. apply DomainProp.
    apply series_cv_shift.
    apply (series_cv_eq (fun n : nat =>
          partialApply (psik (n + S K)%nat) cpx (cpxDpsik (n + S K)%nat))).
    intro n. rewrite Nat.add_comm. reflexivity.
    exact s3.
Qed.

Lemma IntegralTruncateLimitZero
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
  CR_cv _
    (fun n : nat =>
     Integral
       (IntegrableMinConst
          (Xabs f) (CR_of_Q _ (1 # Pos.of_nat (S n)))
          (IntegrableAbs f fInt) (invSuccRealPositive n))) 0.
Proof.
  intros. intro p. destruct (IntegralDense f fInt (2*p)%positive) as [n nmaj].
  destruct (Ilimit IS (Xsum (IntFn (let (intRepres, _) := fInt in intRepres)) n)
                   (LsumStable
                      (IntFn (let (intRepres, _) := fInt in intRepres))
                      (IntFnL (let (intRepres, _) := fInt in intRepres)) n))
    as [_ cv].
  specialize (cv (2*p)%positive) as [k kmaj].
  exists (max n k). intros. unfold CRminus.
  rewrite CRopp_0, CRplus_0_r, CRabs_right.
  apply (CRle_trans _ (Integral
    (IntegrableMinConst (Xabs f)
       (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S (max n k))))
       (IntegrableAbs f fInt) (invSuccRealPositive (max n k))))).
  - apply IntegralNonDecreasing. intros y ydf ydg.
    apply CRmin_glb. rewrite applyXminConst, (DomainProp _ y ydf ydg).
    apply CRmin_l.
    apply (CRle_trans _ (CR_of_Q _ (1 # Pos.of_nat (S i)))).
    apply CRmin_r. apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos.
    apply Pos2Nat.inj_le. rewrite Nat2Pos.id, Nat2Pos.id.
    apply le_n_S, H. discriminate. discriminate.
  - clear H i.
    specialize (nmaj (max n k) (Nat.le_max_l _ _)).
    specialize (kmaj (max n k) (Nat.le_max_r _ _)).
    unfold IntegralDistance in nmaj.
    rewrite <- CRplus_0_r.
    rewrite <- (CRplus_opp_l
                 (CRabs (RealT (ElemFunc IS))
           (I IS _
              (LminConstStable
                 (CR_of_Q (RealT (ElemFunc IS))
                    (1 # Pos.of_nat (S (Init.Nat.max n k))))
                 (Xabs (Xsum (IntFn (let (intRepres, _) := fInt in intRepres)) n))
                 (invSuccRealPositive (Init.Nat.max n k))
                 (LabsStable (ElemFunc IS)
                    (Xsum (IntFn (let (intRepres, _) := fInt in intRepres)) n)
                    (LsumStable (IntFn (let (intRepres, _) := fInt in intRepres))
                       (IntFnL (let (intRepres, _) := fInt in intRepres)) n))) - 0))).
    rewrite <- CRplus_assoc.
    setoid_replace (CR_of_Q (RealT (ElemFunc IS)) (1 # p))
      with (CR_of_Q (RealT (ElemFunc IS)) (1 # (2*p)) + CR_of_Q _ (1 # (2*p))).
    apply CRplus_le_compat. 2: exact kmaj. clear kmaj.
    unfold CRminus. rewrite CRopp_0, CRplus_0_r, CRabs_right.
    rewrite <- IntegralLstable. pose proof (@IntegralMinus IS).
    unfold CRminus in H. rewrite <- H. clear H.
    apply (CRle_trans _ (Integral (IntegrableAbs
              (Xminus (Xsum (IntFn (let (intRepres, _) := fInt in intRepres)) n) f)
              (IntegrableMinus
                 (Xsum (IntFn (let (intRepres, _) := fInt in intRepres)) n) f
                 (IntegrableSum (IntFn (let (intRepres, _) := fInt in intRepres))
                    (fun n : nat =>
                     IntegrableL (IntFn (let (intRepres, _) := fInt in intRepres) n)
                       (IntFnL (let (intRepres, _) := fInt in intRepres) n)) n) fInt)))).
    2: exact nmaj. clear nmaj. apply IntegralNonDecreasing.
    intros y ydf ydg. destruct ydf, ydg.
    rewrite applyXabs. rewrite (applyXminus _ f y d1 d2), CRabs_minus_sym.
    rewrite (applyXminus _ (XminConst (Xabs (Xsum (IntFn (let (intRepres, _) := fInt in intRepres)) n))
          (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S (Init.Nat.max n k))))) y d d0).
    rewrite applyXminConst, applyXminConst.
    apply (CRle_trans _ _ _ (CRle_abs _)).
    apply (CRle_trans _ _ _ (CRmin_contract _ _ _)).
    rewrite (DomainProp f y d2 d), applyXabs.
    rewrite (DomainProp _ y d1 d0), applyXabs.
    apply CRabs_triang_inv2.
    apply integralPositive. intros y ydf. apply CRmin_glb.
    apply CRabs_pos. rewrite <- CR_of_Q_zero. apply CR_of_Q_le.
    discriminate.
    rewrite <- CR_of_Q_plus. apply CR_of_Q_morph. rewrite Qinv_plus_distr.
    reflexivity.
  - apply IntegralNonNeg. intros y ydf. apply CRmin_glb.
    apply CRabs_pos. rewrite <- CR_of_Q_zero. apply CR_of_Q_le.
    discriminate.
Qed.

(* Theorem 1.18 of Bishop *)
Definition IntegrationSpaceCompletion (IS : IntegrationSpace)
  : IntegrationSpace
  := Build_IntegrationSpace
       (FunctionRieszSpaceCompletion IS)
       (fun f fInt => Integral fInt)
       IntegralPlus
       (fun a f fInt => CReq_trans _ ((Integral fInt) * a) _
                                (IntegralScale f fInt a) (CRmult_comm _ _))
       (Ione IS) (IntegrableL (Ione IS) (IoneL IS))
       (CReq_trans _ (I IS (Ione IS) (IoneL IS)) _
                   (IntegralLstable _ _) (IoneInt IS))
       IntegrableContinuous
       (fun f fL => pair (IntegralTruncateLimit f fL)
                      (IntegralTruncateLimitZero f fL)).

(* There is no need to consider integrable functions on
   IntegrationSpaceCompletion, it is only its L functions. *)
Lemma IntegrationSpaceComplete
  : forall (IS : IntegrationSpace) (f : PartialFunction (X (ElemFunc IS))),
    @IntegrableFunction (IntegrationSpaceCompletion IS) f
    -> L (ElemFunc (IntegrationSpaceCompletion IS)) f.
Proof.
  intros IS f fInt. simpl. destruct fInt, x.
  destruct (IntegrableFunctionsComplete IS IntFn IntFnL IntAbsSum IntAbsSumCv).
  exists x. destruct x. simpl. simpl in p0.
  apply (PartialRestriction_trans _ _ (XinfiniteSumAbs IntFn)).
  apply p0. exact p.
Qed.
