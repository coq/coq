(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(*
  We provide the standard constructive integration space on the real
  numbers. This is the constructive expression of the Lebesgue measure.

  The elementary functions are the uniformly continuous functions R -> R
  with compact support, with the canonical definition of the integral
  in this case : the difference of anti-derivatives.

  It is the example given by Bishop and Cheng, page 67 of
  their article. Working in R rather than in a locally
  compact space X simplifies the proof, because we replace
  compact sets by segments (thus skipping the theory of profiles).

  One might be tempted to restrict to piecewise linear functions with
  compact support, however one cannot constructively prove that those
  are stable under absolute value. It would require exact comparisons
  of the values of the functions with zero.
 *)

Require Import QArith Qminmax Qpower Qabs.

Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructiveDiagonal.
Require Import ConstructivePartialFunctions.
Require Import ConstructiveUniformCont.
Require Import ConstructiveCauchyIntegral.
Require Import CMTbase.
Require Import CMTPositivity.
Require Import CMTIntegrableFunctions.
Require Import CMTFullSets.
Require Import CMTIntegrableSets.

Local Open Scope ConstructiveReals.


Record Is_CSUC_func {R : ConstructiveReals}
       (f : PartialFunction (CRcarrier R)) : Type :=
  {
    CSUC_fullDomain : forall x : CRcarrier R, Domain f x;
    CSUC_low : CRcarrier R;
    CSUC_high : CRcarrier R;
    (* The zero function has an empty support, but we
       can extend it to a point. A nonempty support allows
       to define its distance to a point. *)
    CSUC_lowHigh : CSUC_low <= CSUC_high;
    CSUC_cont_mod : forall x:CRcarrier R, 0 < x -> CRcarrier R;
    CSUC_adapt : CSUC (TotalizeFunc (CRcarrier R) f CSUC_fullDomain)
                      CSUC_low CSUC_high CSUC_cont_mod;
  }.

Definition CSUC_func_plus_stable
  : forall {R : ConstructiveReals} (f g : PartialFunction (CRcarrier R)),
    Is_CSUC_func f -> Is_CSUC_func g -> Is_CSUC_func (Xplus f g).
Proof.
  intros R [df f injPrF] [dg g injPrG]
         [fullDomF lowF highF lowHighF modF]
         [fullDomG lowG highG lowHighG modG].
  assert (CRmin lowF lowG <= CRmax highF highG) as sumLowHigh.
  { apply (CRle_trans _ lowF). apply CRmin_l.
    apply (CRle_trans _ highF). apply lowHighF. apply CRmax_l. }
  apply (Build_Is_CSUC_func
           R (Xplus
       {| Domain := df; partialApply := f; DomainProp := injPrF |}
       {| Domain := dg; partialApply := g; DomainProp := injPrG |})
           (fun x => pair (fullDomF x) (fullDomG x))
           (CRmin lowF lowG) (CRmax highF highG) sumLowHigh
           (fun x xPos => CRmin (modF (x * CR_of_Q R (1#2)) (eps2_Rgt_R0 x xPos))
                            (modG (x * CR_of_Q R (1#2)) (eps2_Rgt_R0 x xPos)))).
  split.
  - apply UC_plus. apply CSUC_adapt0. apply CSUC_adapt1.
  - intros. simpl.
    destruct CSUC_adapt0 as [H0 H1]. simpl in H1. rewrite H1.
    destruct CSUC_adapt1 as [H2 H3]. simpl in H3. rewrite H3.
    rewrite CRplus_0_l. reflexivity.
    destruct H as [H|H].
    left. apply (CRlt_le_trans x _ _ H). apply CRmin_r.
    right.
    apply (CRle_lt_trans _ (CRmax highF highG)).
    apply CRmax_r. apply H.
    destruct H as [H|H]. left. apply (CRlt_le_trans x _ _ H).
    apply CRmin_l. right.
    apply (CRle_lt_trans _ (CRmax highF highG)).
    apply CRmax_l. apply H.
Defined.

Definition CSUC_func_abs_stable
  : forall {R : ConstructiveReals} (f : PartialFunction (CRcarrier R)),
    Is_CSUC_func f -> Is_CSUC_func (Xabs f).
Proof.
  intros R f H. destruct H, f.
  apply (Build_Is_CSUC_func
           R (Xabs
       {|
       Domain := Domain;
       partialApply := partialApply;
       DomainProp := DomainProp |})
           CSUC_fullDomain0
           CSUC_low0 CSUC_high0 CSUC_lowHigh0 CSUC_cont_mod0).
  destruct CSUC_adapt0. split. split.
  - intro x. apply (fst u).
  - intros. simpl.
    apply (CRle_lt_trans _ _ _ (CRabs_triang_inv2 _ _)).
    destruct u.
    apply (c1 _ _ _ epsPos). apply H.
  - intros. simpl. destruct u. simpl in c. rewrite c.
    apply CRabs_right. apply CRle_refl. apply H.
Defined.

Definition CSUC_func_min_stable
  : forall {R : ConstructiveReals} (f : PartialFunction (CRcarrier R)),
    Is_CSUC_func f -> Is_CSUC_func (XminConst f 1).
Proof.
  intros R f H. destruct H,f.
  apply (Build_Is_CSUC_func
           R (XminConst
       {|
       Domain := Domain;
       partialApply := partialApply;
       DomainProp := DomainProp |} 1)
           CSUC_fullDomain0
           CSUC_low0 CSUC_high0 CSUC_lowHigh0 CSUC_cont_mod0).
  destruct CSUC_adapt0. split. split.
  - intro x. apply (fst u).
  - intros. simpl.
    apply (CRle_lt_trans _ (CRabs _ (partialApply x (CSUC_fullDomain0 x)
                                     - partialApply y (CSUC_fullDomain0 y)))).
    apply CRmin_contract.
    destruct u. apply (c1 _ _ _ epsPos). apply H.
  - intros. simpl in c.
    unfold TotalizeFunc, XminConst, Xop, ConstructivePartialFunctions.partialApply.
    rewrite c. apply CRmin_left.
    apply CRlt_asym, CRzero_lt_one. apply H.
Defined.

Definition CSUC_func_scale {R : ConstructiveReals} (a : CRcarrier R)
           (f : PartialFunction (CRcarrier R))
  : Is_CSUC_func f -> Is_CSUC_func (Xscale a f).
Proof.
  intros H. destruct H,f.

  apply (Build_Is_CSUC_func
           R (Xscale a
       {|
       Domain := Domain;
       partialApply := partialApply;
       DomainProp := DomainProp |})
           CSUC_fullDomain0
           CSUC_low0 CSUC_high0 CSUC_lowHigh0
           (fun (eps:CRcarrier R) epsPos
            => CSUC_cont_mod0 (eps * CRinv R (CRmax 1 (CRabs _ a)) (inr (posScale a)))
                            (CRmult_lt_0_compat _
                                        eps _ epsPos (CRinv_0_lt_compat _
                                                        _ (inr (posScale a)) (posScale a))))).
  destruct CSUC_adapt0. split.
  - apply UC_scale. exact u.
  - intros. simpl. simpl in c. rewrite c.
    rewrite CRmult_0_r. reflexivity. exact H.
Defined.

Lemma CSUCext :
  forall {R : ConstructiveReals} (f g : PartialFunction (CRcarrier R)),
    PartialFunExtEq f g -> Is_CSUC_func f -> Is_CSUC_func g.
Proof.
  intros R f g H H0. destruct f,g,H,H0,p; simpl in d.
  simpl in CSUC_fullDomain0.
  apply (Build_Is_CSUC_func R
          {|
    Domain := Domain0;
    partialApply := partialApply0;
    DomainProp := DomainProp0 |}
          (fun x => d x (CSUC_fullDomain0 x)) CSUC_low0 CSUC_high0
          CSUC_lowHigh0 CSUC_cont_mod0).
  split.
  apply (UC_ext (TotalizeFunc (CRcarrier R)
       {|
       Domain := Domain;
       partialApply := partialApply;
       DomainProp := DomainProp |} CSUC_fullDomain0)).
  apply CSUC_adapt0. intro x. simpl.
  apply c.
  intros. simpl. destruct CSUC_adapt0. simpl in c, c0.
  rewrite <- (c x (CSUC_fullDomain0 x)). apply c0. exact H.
Defined.

Definition ElemCSUC {R : ConstructiveReals}
  : FunctionRieszSpace.
Proof.
  apply (Build_FunctionRieszSpace
           (CRcarrier R) R Is_CSUC_func).
  - apply CSUCext.
  - apply CSUC_func_plus_stable.
  - apply CSUC_func_abs_stable.
  - apply CSUC_func_min_stable.
  - apply CSUC_func_scale.
Defined.

Definition IntegralCSUC {R : ConstructiveReals}
           (f : PartialFunction (CRcarrier R)) (fCSUC : Is_CSUC_func f) : CRcarrier R
  := UC_integral
       (TotalizeFunc (CRcarrier R) f (CSUC_fullDomain _ fCSUC))
       (CSUC_low _ fCSUC) (CSUC_high _ fCSUC)
       (CSUC_cont_mod _ fCSUC)
       (fst (CSUC_adapt _ fCSUC))
       (CSUC_lowHigh _ fCSUC).

(* Extend the support *)
Lemma CSUCextendAdapt : forall {R : ConstructiveReals} (f : PartialFunction (CRcarrier R))
                          (fL : Is_CSUC_func f)
                          (a b : CRcarrier R),
    a <= CSUC_low f fL
    -> CSUC_high f fL <= b
    -> CSUC (TotalizeFunc (CRcarrier R) f (CSUC_fullDomain f fL)) a b
           (CSUC_cont_mod f fL).
Proof.
  split. split.
  - apply fL.
  - apply fL.
  - intros. destruct fL,CSUC_adapt0,u.
    simpl. simpl in H,H0. rewrite (c x).
    reflexivity. destruct H1. left. exact (CRlt_le_trans x a _ c2 H).
    right. exact (CRle_lt_trans _ b x H0 c2).
Qed.

Lemma CSUCextendSupport : forall {R : ConstructiveReals} (f : PartialFunction (CRcarrier R))
                            (fL : Is_CSUC_func f)
                            (a b : CRcarrier R)
                            (aBelow : a <= CSUC_low f fL)
                            (bAbove : CSUC_high f fL <= b)
                            (leab : a <= b), (* redundant *)
    IntegralCSUC f fL
    == UC_integral
        (TotalizeFunc (CRcarrier R) f (CSUC_fullDomain f fL))
        a b (CSUC_cont_mod f fL)
        (fst (CSUCextendAdapt f fL a b aBelow bAbove)) leab.
Proof.
  (* Use Chasles relation *)
  intros.
  assert (CSUC_low f fL <= b).
  { apply (CRle_trans _ (CSUC_high f fL)).
    apply CSUC_lowHigh. apply bAbove. }
  rewrite (UC_integral_chasles a (CSUC_low f fL) b
                               _ _ _ aBelow H).
  rewrite (UC_integral_chasles (CSUC_low f fL) (CSUC_high f fL) b
                               _ _ _ (CSUC_lowHigh f fL) bAbove).
  rewrite (UC_integral_zero _ a (CSUC_low f fL)).
  rewrite (UC_integral_zero _ (CSUC_high f fL) b).
  rewrite CRplus_0_l, CRplus_0_r.
  apply (UC_integral_extens
           (TotalizeFunc (CRcarrier R) f (CSUC_fullDomain f fL))
           (TotalizeFunc (CRcarrier R) f (CSUC_fullDomain f fL))
           (CSUC_low f fL) (CSUC_high f fL)).
  - intros. reflexivity.
  - intros.
    apply (CSUC_connect_support
             _ (CSUC_low f fL)
             (CSUC_high f fL) (CSUC_cont_mod f fL)).
    apply fL. right. apply H0.
  - intros.
    apply (CSUC_connect_support
             _ (CSUC_low f fL)
             (CSUC_high f fL) (CSUC_cont_mod f fL)).
    apply fL. left. apply H0.
Qed.

Lemma CSUCIntegralAdditive : forall {R : ConstructiveReals}
                               (f g : PartialFunction (CRcarrier R))
                               (fL : Is_CSUC_func f)
                               (gL : Is_CSUC_func g),
    IntegralCSUC (Xplus f g) (CSUC_func_plus_stable f g fL gL)
    == IntegralCSUC f fL + IntegralCSUC g gL.
Proof.
  intros.
  pose (CRmin (CSUC_low f fL) (CSUC_low g gL)) as c.
  pose (CRmax (CSUC_high f fL) (CSUC_high g gL)) as d.
  assert (c <= d).
  { apply (CRle_trans _ (CSUC_low f fL)). apply CRmin_l.
    apply (CRle_trans _ (CSUC_high f fL)). apply (CSUC_lowHigh f fL).
    apply CRmax_l. }
  (* Integrate f and g on [c,d], with same integral because
     they equal 0 outside their supports. *)
  rewrite (CSUCextendSupport f fL c d (CRmin_l _ _) (CRmax_l _ _) H).
  rewrite (CSUCextendSupport g gL c d (CRmin_r _ _) (CRmax_r _ _) H).
  transitivity (UC_integral
                  (fun x => TotalizeFunc (CRcarrier R) f (CSUC_fullDomain f fL) x
                         + TotalizeFunc (CRcarrier R) g (CSUC_fullDomain g gL) x)
                  (CSUC_low (Xplus f g) (CSUC_func_plus_stable f g fL gL))
                  (CSUC_high (Xplus f g) (CSUC_func_plus_stable f g fL gL))
                  _ (UC_plus _ _ _ _ (fst (CSUC_adapt f fL))
                             (fst (CSUC_adapt g gL)))
                  (CSUC_lowHigh (Xplus f g) (CSUC_func_plus_stable f g fL gL))).
  unfold IntegralCSUC.
  apply (UC_integral_extens
           (TotalizeFunc (CRcarrier R) (Xplus f g)
                         (CSUC_fullDomain (Xplus f g) (CSUC_func_plus_stable f g fL gL)))
           (fun x : CRcarrier R =>
              TotalizeFunc (CRcarrier R) f (CSUC_fullDomain f fL) x +
              TotalizeFunc (CRcarrier R) g (CSUC_fullDomain g gL) x)).
  - intros. destruct f,g,fL,gL; reflexivity.
  - destruct f,g,fL,gL; apply UC_integral_plus.
Qed.

Lemma CSUCIntegralAdditiveIterate
  : forall {R : ConstructiveReals} (fn : nat -> @PartialFunction R (X ElemCSUC))
      (fnL : forall n : nat, L ElemCSUC (fn n)) (N : nat),
    IntegralCSUC (Xsum fn N) (LsumStable fn fnL N)
    == CRsum (fun n : nat => IntegralCSUC (fn n) (fnL n)) N.
Proof.
  induction N.
  - reflexivity.
  - simpl. rewrite <- IHN.
    rewrite CSUCIntegralAdditive. reflexivity.
Qed.

Lemma CSUC_bound_ext
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (a b c d : CRcarrier R) (cont_mod : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    a == c
    -> b == d
    -> CSUC f a b cont_mod
    -> CSUC f c d cont_mod.
Proof.
  intros. destruct H1. split. exact u.
  intros. destruct H1. rewrite <- H in c1. apply c0.
  left. exact c1. rewrite <- H0 in c1. apply c0. right. exact c1.
Qed.

Definition CSUCTrapeze_IS_CSUC
           {R : ConstructiveReals} (a b eta : CRcarrier R) (etaPos : 0 < eta)
  : a <= b -> Is_CSUC_func (PartializeFunc (CRcarrier R)
                                           (CSUCUnitTrapeze a b eta etaPos))
  := fun leab => Build_Is_CSUC_func
           R (PartializeFunc (CRcarrier R)
                             (CSUCUnitTrapeze a b eta etaPos))
           (fun x:CRcarrier R => Logic.I)
           (a-eta) (b+eta) (TrapezeLe a b eta etaPos leab)
           (* The modulus could be improved to eps *)
           (fun eps epsPos => eps * CR_of_Q R (1#2) * eta)
           (CSUCTrapeze_CSUC a b eta etaPos leab).

Lemma CSUCIntegralHomogeneous
  : forall {R : ConstructiveReals} (a : CRcarrier R) (f : PartialFunction (CRcarrier R))
      (fL : Is_CSUC_func f),
    IntegralCSUC (Xscale a f) (CSUC_func_scale a f fL)
    == a * IntegralCSUC f fL.
Proof.
  intros. (* Get the a inside to the right *)
  unfold IntegralCSUC.
  rewrite <- UC_integral_scale.
  destruct f,fL; apply UC_integral_extens; reflexivity.
Qed.

Section CSUCContinuous. (* Hide the details of this proof *)

  Variable (R : ConstructiveReals)
           (g : CRcarrier R -> CRcarrier R)
           (fn : nat -> CRcarrier R -> CRcarrier R)
           (fnPos : forall (k:nat) (x:CRcarrier R), 0 <= fn k x)
           (fnMod : nat -> forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
           (fnCont : forall n:nat, UniformCont (fn n) (fnMod n))
           (gMod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
           (a b : CRcarrier R)
           (leab : a <= b)
           (gCSUC : CSUC g a b gMod)
           (majInt : series_cv_lim_lt (fun k : nat => UC_integral
                                                   (fn k) a b
                                                   (fnMod k) (fnCont k) leab)
                                      (UC_integral
                                         g a b
                                         gMod (fst gCSUC) leab)).

(* An interval where the searched point is *)
Record CSUCposPointApprox
  : Set :=
  { x : CRcarrier R;
    y : CRcarrier R;
    lexy : x <= y;

    lambdaInfiniteMaj :
      series_cv_lim_lt (fun k : nat => UC_integral
                                    (fn k) x y
                                    (fnMod k) (fnCont k) lexy)
                       (UC_integral
                          g x y
                          gMod (fst gCSUC) lexy);
  }.


Definition CSUCposPointApproxInit
  : CSUCposPointApprox
  := Build_CSUCposPointApprox a b leab majInt.

Lemma LocalizeIntegralSeries
  : forall (x y z t : CRcarrier R) (infint : CRcarrier R)
      (lexy : x <= y) (lezt : z <= t),
    x <= z
    -> t <= y
    -> series_cv (fun k : nat => UC_integral
                             (fn k) x y
                             (fnMod k) (fnCont k) lexy)
                infint
    -> { sLoc : CRcarrier R & series_cv (fun k : nat => UC_integral
                              (fn k) z t
                              (fnMod k) (fnCont k) lezt)
                                    sLoc }.
Proof.
  intros.
  destruct (series_cv_maj (fun k : nat => UC_integral
                              (fn k) z t
                              (fnMod k) (fnCont k) lezt)
                          (fun k : nat => UC_integral
                                       (fn k) x0 y0
                                       (fnMod k) (fnCont k) lexy0)
                           infint).
  - intros. rewrite CRabs_right.
    apply (UC_integral_extend_nonneg (fn n) (fnMod n)).
    exact H. exact H0. apply fnPos.
    apply UC_integral_pos.
    intros. apply fnPos.
  - exact H1.
  - exists x1. apply p.
Qed.


Definition CSUCposPointApproxStep
           (n : nat)
           (currStep : CSUCposPointApprox)
  : { nextApprox : CSUCposPointApprox
    | x currStep <= x nextApprox
      /\ y nextApprox <= y currStep
      /\ y nextApprox - x nextApprox == (y currStep - x currStep) * CR_of_Q R (1#2) }.
Proof.
  clear majInt. destruct currStep, lambdaInfiniteMaj0, p as [i r].
  assert (x0 <= (x0+y0) * CR_of_Q R (1#2)).
  { apply (CRmult_le_reg_r (CR_of_Q R 2)). apply CR_of_Q_pos. reflexivity.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l, CRmult_1_r, CRmult_1_r.
    apply CRplus_le_compat_l. exact lexy0. }
  assert ((x0+y0) * CR_of_Q R (1#2) <= y0).
  { apply (CRmult_le_reg_r (CR_of_Q R 2)). apply CR_of_Q_pos. reflexivity.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l, CRmult_1_r, CRmult_1_r.
    apply CRplus_le_compat_r. exact lexy0. }
  destruct (LocalizeIntegralSeries
              x0 y0 x0 ((x0+y0)*CR_of_Q R (1#2)) x1 lexy0 H (CRle_refl x0)).
  exact H0. exact i.
  destruct (LocalizeIntegralSeries
              x0 y0 ((x0+y0) * CR_of_Q R (1#2)) y0 x1 lexy0 H0 H).
  apply CRle_refl. exact i.
  assert (x1 == x2 + x3) as H1.
  { apply (CR_cv_unique _ _ _ i).
    apply (series_cv_eq
             (fun k : nat => UC_integral (fn k) x0 ((x0 + y0) * CR_of_Q R (1#2)) (fnMod k) (fnCont k) H
                        + (UC_integral (fn k) ((x0 + y0) * CR_of_Q R (1#2)) y0 (fnMod k) (fnCont k) H0))).
    intros. symmetry. apply UC_integral_chasles.
    apply series_cv_plus. exact s. exact s0. }
  simpl. rewrite H1 in r.
  rewrite (UC_integral_chasles
             x0 ((x0+y0) * CR_of_Q R (1#2)) y0 _ _ _ H H0) in r.
  apply Rplus_lt_epsilon in r.
  assert ((y0 - x0) * CR_of_Q R (1 # 2) <= (x0 + y0) * CR_of_Q R (1 # 2) - x0).
  { apply (CRmult_le_reg_r (CR_of_Q R 2)). apply CR_of_Q_pos. reflexivity.
    unfold CRminus. rewrite CRmult_plus_distr_r, CRmult_plus_distr_r.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRmult_plus_distr_r, CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_1_r, CRmult_1_r, CRmult_1_r.
    rewrite (CRplus_comm x0), CRplus_assoc. apply CRplus_le_compat_l.
    rewrite CRmult_plus_distr_l, CRmult_1_r, <- CRplus_assoc, CRplus_opp_r.
    rewrite CRplus_0_l. apply CRle_refl. }
  destruct r.
  - assert (series_cv_lim_lt
    (fun k : nat => UC_integral (fn k) x0 ((x0 + y0) * CR_of_Q R (1#2)) (fnMod k) (fnCont k) H)
    (UC_integral g x0 ((x0 + y0) * CR_of_Q R (1#2)) gMod (fst gCSUC) H)).
    { exists x2. split. exact s. exact c. }
    exists (Build_CSUCposPointApprox x0 ((x0 + y0) * CR_of_Q R (1#2)) H H3).
    simpl. repeat split. apply CRle_refl. exact H0.
    exact H2.
    apply (CRmult_le_reg_r (CR_of_Q R 2)). apply CR_of_Q_pos. reflexivity.
    unfold CRminus. rewrite CRmult_plus_distr_r, CRmult_plus_distr_r.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRmult_plus_distr_r, CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRmult_plus_distr_r, CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_1_r, CRmult_1_r, CRmult_1_r.
    rewrite (CRplus_comm x0), CRplus_assoc. apply CRplus_le_compat_l.
    rewrite CRmult_plus_distr_l, CRmult_1_r, <- CRplus_assoc, CRplus_opp_r.
    rewrite CRplus_0_l. apply CRle_refl.
  - assert (series_cv_lim_lt
    (fun k : nat => UC_integral (fn k) ((x0 + y0) * CR_of_Q R (1#2)) y0 (fnMod k) (fnCont k) H0)
    (UC_integral g ((x0 + y0) * CR_of_Q R (1#2)) y0 gMod (fst gCSUC) H0)).
    { exists x3. split. exact s0. exact c. }
    exists (Build_CSUCposPointApprox ((x0 + y0) * CR_of_Q R (1#2)) y0 H0 H3).
    simpl. repeat split. exact H. apply CRle_refl.
    apply (CRmult_le_reg_r (CR_of_Q R 2)). apply CR_of_Q_pos. reflexivity.
    unfold CRminus. rewrite CRmult_plus_distr_r, CRmult_plus_distr_r.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRmult_plus_distr_r, CRopp_mult_distr_l, CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_1_r, CRmult_1_r, CRmult_1_r.
    rewrite CRopp_plus_distr.
    rewrite (CRplus_comm (-x0)), <- CRplus_assoc. apply CRplus_le_compat_r.
    rewrite CRmult_plus_distr_l, CRmult_1_r, CRplus_assoc, CRplus_opp_r.
    rewrite CRplus_0_r. apply CRle_refl.
    apply (CRmult_le_reg_r (CR_of_Q R 2)). apply CR_of_Q_pos. reflexivity.
    unfold CRminus. rewrite CRmult_plus_distr_r, CRmult_plus_distr_r.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRopp_plus_distr, CRmult_plus_distr_r, CRopp_mult_distr_l, CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRopp_mult_distr_l, CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_1_r, CRmult_1_r, CRmult_1_r.
    rewrite (CRplus_comm (-x0)), <- CRplus_assoc. apply CRplus_le_compat_r.
    rewrite CRmult_plus_distr_l, CRmult_1_r, CRplus_assoc, CRplus_opp_r.
    rewrite CRplus_0_r. apply CRle_refl.
Qed.

Definition CSUCposPointApproxSequence
  : nat -> CSUCposPointApprox
  := nat_rec _ CSUCposPointApproxInit
             (fun (n:nat) currStep => proj1_sig (CSUCposPointApproxStep n currStep)).

(* The segments are nested, so the centers form a Cauchy sequence. *)
Lemma CSUCposPointApproxSequenceNested
  : forall n p : nat,
    x (CSUCposPointApproxSequence n) <= x (CSUCposPointApproxSequence (n + p))
    /\ y (CSUCposPointApproxSequence (n+p)) <= y (CSUCposPointApproxSequence n).
Proof.
  intros. generalize dependent n. induction p.
  - intros. rewrite Nat.add_0_r.
    destruct (CSUCposPointApproxSequence n).
    split; apply CRle_refl.
  - intro n. rewrite Nat.add_succ_r. simpl. specialize (IHp n).
    destruct (CSUCposPointApproxSequence n).
    destruct (CSUCposPointApproxStep (n + p) (CSUCposPointApproxSequence (n + p))).
    destruct (CSUCposPointApproxSequence (n+p)), x1.
    simpl. simpl in a0. split. apply (CRle_trans _ x2).
    apply IHp. apply a0. apply (CRle_trans _ y1). apply a0. apply IHp.
Qed.

Lemma CSUCposPointApproxSequenceLength
  : forall n:nat, (y (CSUCposPointApproxSequence n) - x (CSUCposPointApproxSequence n)
            == (b-a) * CR_of_Q R (/2^Z.of_nat n)).
Proof.
  induction n.
  - simpl. rewrite CR_of_Q_one, CRmult_1_r. reflexivity.
  - rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite Qpower_plus.
    simpl. destruct (CSUCposPointApproxStep n (CSUCposPointApproxSequence n)); simpl.
    destruct a0, H0. unfold Qdiv.
    rewrite Qinv_mult_distr, CR_of_Q_mult, <- CRmult_assoc, <- IHn. clear IHn.
    exact H1. discriminate.
Qed.

Lemma CSUCposPointApproxSequenceCvZero
  : forall n : positive,
    { p : nat &
      forall i : nat,
        (p <= i)%nat ->
        CRabs R (y (CSUCposPointApproxSequence i) - x (CSUCposPointApproxSequence i))
         < CR_of_Q R (1 # n) }.
Proof.
  intros n.
  destruct (CRup_nat (b - a)) as [i imaj].
  destruct i. exfalso.
  simpl in imaj. rewrite CR_of_Q_zero in imaj.
  rewrite <- (CRplus_opp_r a) in imaj.
  apply CRplus_lt_reg_r in imaj. contradiction.
  destruct (@GeoCvZero R (Pos.of_nat (S i)*n)%positive) as [p pmaj].
  exists p. intros.
  apply (CRle_lt_trans _ ((b-a)* CR_of_Q R ((/2)^Z.of_nat p))).
  - rewrite Qinv_power.
    pose proof (CSUCposPointApproxSequenceLength p).
    rewrite <- H0. clear H0.
    destruct (Nat.le_exists_sub p i0 H), H0. subst i0.
    apply Rsmaller_interval.
    rewrite Nat.add_comm. apply CSUCposPointApproxSequenceNested.
    apply (CRle_trans _ (y (CSUCposPointApproxSequence (x0 + p)))).
    destruct (CSUCposPointApproxSequence (x0 + p)); simpl. exact lexy0.
    rewrite Nat.add_comm. apply CSUCposPointApproxSequenceNested.
    apply (CRle_trans _ (x (CSUCposPointApproxSequence (x0+p)))).
    rewrite Nat.add_comm. apply CSUCposPointApproxSequenceNested.
    destruct (CSUCposPointApproxSequence (x0 + p)); simpl. exact lexy0.
    rewrite Nat.add_comm. apply CSUCposPointApproxSequenceNested.
  - specialize (pmaj p (le_refl p)).
    unfold CRminus in pmaj. rewrite CRopp_0, CRplus_0_r in pmaj.
    apply (CRlt_le_trans _ (CR_of_Q R ((Z.of_nat (S i) # 1) * (/ 2) ^ Z.of_nat p ))).
    rewrite CR_of_Q_mult.
    apply CRmult_lt_compat_r. 2: exact imaj.
    apply CR_of_Q_pos. apply Qpower_positive. reflexivity.
    rewrite CRabs_right in pmaj.
    2: apply CRlt_asym, pow_lt; exact Rlt_0_half.
    apply CR_of_Q_le.
    setoid_replace (CRpow (CR_of_Q R (1 # 2)) p)
      with (CR_of_Q R ((/ 2) ^ Z.of_nat p )) in pmaj.
    destruct (Q_dec ((/ 2) ^ Z.of_nat p) (1 # Pos.of_nat (S i) * n)). destruct s.
    apply (Qmult_lt_l _ _ (Z.of_nat (S i) # 1)) in q.
    apply (Qle_trans _ ((Z.of_nat (S i) # 1) * (1 # Pos.of_nat (S i) * n))%Q).
    apply Qlt_le_weak, q. 2: reflexivity.
    unfold Qmult, Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_l, Pos.mul_1_l.
    rewrite Pos2Z.inj_mul. unfold Z.of_nat.
    rewrite Pos.of_nat_succ. apply Z.le_refl.
    exfalso. apply (CR_of_Q_lt R) in q. apply pmaj, q.
    rewrite q.
    unfold Qmult, Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_l, Pos.mul_1_l.
    rewrite Pos2Z.inj_mul. unfold Z.of_nat.
    rewrite Pos.of_nat_succ. apply Z.le_refl.
    rewrite pow_inject_Q. reflexivity. discriminate.
Qed.

Lemma CSUCposPointApproxSequenceCauchy
  : { l : CRcarrier R
          &  CR_cv R (fun n => x (CSUCposPointApproxSequence n)) l }.
Proof.
  apply (CR_complete R (fun n => x (CSUCposPointApproxSequence n))).
  intros n.
  destruct (CSUCposPointApproxSequenceCvZero n) as [p pmaj].
  exists p. intros.
  apply (CRle_trans _ (y (CSUCposPointApproxSequence p)
                       - x (CSUCposPointApproxSequence p))).
  - destruct (Nat.le_exists_sub p j H0), H1. subst j.
    destruct (Nat.le_exists_sub p i H), H1. subst i.
    apply Rsmaller_interval.
    rewrite Nat.add_comm. apply CSUCposPointApproxSequenceNested.
    apply (CRle_trans _ (y (CSUCposPointApproxSequence (x0 + p)))).
    destruct (CSUCposPointApproxSequence (x0 + p)); simpl. exact lexy0.
    rewrite Nat.add_comm. apply CSUCposPointApproxSequenceNested.
    rewrite Nat.add_comm. apply CSUCposPointApproxSequenceNested.
    apply (CRle_trans _ (y (CSUCposPointApproxSequence (x1 + p)))).
    destruct (CSUCposPointApproxSequence (x1 + p)); simpl. exact lexy0.
    rewrite Nat.add_comm. apply CSUCposPointApproxSequenceNested.
  - specialize (pmaj p (le_refl p)). unfold CRminus in pmaj.
    unfold CRminus. apply CRlt_asym.
    exact (CRle_lt_trans _ _ _ (CRle_abs _) pmaj).
Qed.

Lemma CSUCposPointApproxLimitNested
  : forall n : nat,
    let (l,_) := CSUCposPointApproxSequenceCauchy in
    x (CSUCposPointApproxSequence n) <= l
    /\ l <= y (CSUCposPointApproxSequence n).
Proof.
  intro n. pose proof (CSUCposPointApproxSequenceNested n).
  destruct CSUCposPointApproxSequenceCauchy
    as [l lcv], (CSUCposPointApproxSequence n); simpl.
  split.
  - apply (CR_cv_bound_down
             (fun n : nat => x (CSUCposPointApproxSequence n)) _ _ n).
    intros. destruct (Nat.le_exists_sub n n0 H0). destruct H1. subst n0.
    rewrite plus_comm. specialize (H x1).
    destruct (CSUCposPointApproxSequence (n + x1)); simpl; simpl in H.
    apply H. apply lcv.
  - apply (CR_cv_bound_up
             (fun n : nat => x (CSUCposPointApproxSequence n)) _ _ n).
    intros. destruct (Nat.le_exists_sub n n0 H0). destruct H1. subst n0.
    rewrite plus_comm. specialize (H x1).
    destruct (CSUCposPointApproxSequence (n + x1)); simpl; simpl in H.
    apply (CRle_trans _ y1). exact lexy1. apply H. apply lcv.
Qed.

Lemma CSUCIcontinuous :
  let (l,_) := CSUCposPointApproxSequenceCauchy in
  forall k:nat, CRsum (fun n => fn n l) k <= g l.
Proof.
  pose proof CSUCposPointApproxLimitNested.
  destruct CSUCposPointApproxSequenceCauchy as [l lcv].
  intro k. intro abs.
  destruct (UC_sum (fun n x => fn n x) fnMod fnCont k) as [modS contS].
  destruct (EnlargePointMajoration g _ l gMod modS (fst gCSUC) contS abs)
    as [eta [etaPos etaMaj]].
  (* Put the approximation's integral domain inside eta *)
  destruct (CRup_nat (CRinv R eta (inr etaPos))) as [p pmaj].
  assert (0 < @INR R p) as qpPos.
  { apply (CRlt_trans _ (CRinv R eta (inr etaPos))).
    apply CRinv_0_lt_compat. exact etaPos. exact pmaj. }
  assert (0 < p)%nat.
  { unfold INR in qpPos. destruct (Q_dec 0 (Z.of_nat p # 1)). destruct s.
    unfold Qlt,Qnum,Qden in q.
    simpl in q. rewrite Z.mul_1_r in q. apply Nat2Z.inj_lt.
    exact q. exfalso. rewrite <- CR_of_Q_zero in qpPos.
    apply (CR_of_Q_lt R) in q. exact (CRlt_asym _ _ q qpPos).
    exfalso. rewrite <- q, CR_of_Q_zero in qpPos.
    exact (CRlt_asym _ _ qpPos qpPos). }
  destruct (CSUCposPointApproxSequenceCvZero (Pos.of_nat p)) as [i imaj].
  specialize (imaj i (le_refl i)). specialize (H i).
  destruct (CSUCposPointApproxSequence i); unfold x,y in imaj.
  destruct lambdaInfiniteMaj0. simpl in H.
  assert (CRsum (fun j : nat => UC_integral (fn j) x0 y0
                                               (fnMod j) (fnCont j) lexy0) k
          < UC_integral g x0 y0 gMod (fst gCSUC) lexy0).
  { apply (CRle_lt_trans _ x1). 2: apply p0.
    apply growing_ineq. 2: apply p0.
    intros n.
    rewrite <- (CRplus_0_r (CRsum (fun j : nat => UC_integral (fn j) x0 y0
                                                           (fnMod j) (fnCont j)
                                                           lexy0) n)).
    apply CRplus_le_compat_l. apply UC_integral_pos.
    intros. apply fnPos. }
  assert (forall x y : CRcarrier R, x < y -> ~(y<=x)) as CReal_lt_not_le.
  { intros. intro abs1. contradiction. }
  apply (CReal_lt_not_le _ _ H1).
  destruct (UC_sum fn fnMod fnCont k) as [modSk c].
  rewrite <- (UC_integral_sum fn _ _ k _ _ fnCont c).
  apply UC_integral_nonneg.
  intros. apply CRlt_asym, etaMaj.
  rewrite CRabs_right in imaj.
  apply (CRle_lt_trans _ (y0- x0)).
  apply Rsmaller_interval.
  apply H2. apply H2. apply H. apply H.
  apply (CRlt_trans _ (CR_of_Q R (1#Pos.of_nat p))).
  unfold CRminus. exact imaj.
  2: rewrite <- (CRplus_opp_r x0); apply CRplus_le_compat_r, lexy0.
  apply (CRmult_lt_compat_l eta) in pmaj.
  rewrite CRinv_r in pmaj. 2: exact etaPos.
  apply (CRmult_lt_reg_r (INR p)).
  exact qpPos.
  apply (CRle_lt_trans _ 1). 2: exact pmaj.
  unfold INR. rewrite <- CR_of_Q_mult, <- CR_of_Q_one. apply CR_of_Q_le.
  unfold Qmult, Qle, Qden, Qnum. rewrite Z.mul_1_l, Z.mul_1_l, Pos.mul_1_r.
  rewrite Z.mul_1_r. rewrite <- positive_nat_Z.
  rewrite Nat2Pos.id. apply Z.le_refl. intro abs1.
  subst p. inversion H0.
Qed.

(* Workaround a destruct problem *)
Lemma DestructCSUCposPoint :
  { l : CRcarrier R
  | (forall k:nat, CRsum (fun n => fn n l) k <= g l)
    /\ x (CSUCposPointApproxSequence 0) <= l
    /\ l <= y (CSUCposPointApproxSequence 0) }.
Proof.
  pose proof CSUCIcontinuous.
  pose proof CSUCposPointApproxLimitNested.
  destruct CSUCposPointApproxSequenceCauchy as [l lcv].
  exists l. split. exact H. apply H0.
Qed.

End CSUCContinuous.


Lemma CSUC_extend_pos
  : forall {R : ConstructiveReals} (f : PartialFunction (CRcarrier R))
      (fL : Is_CSUC_func f) (a b : CRcarrier R) (leab : a <= b),
    nonNegFunc f
    -> UC_integral (TotalizeFunc (CRcarrier R) f (CSUC_fullDomain f fL))
                         a b (CSUC_cont_mod f fL)
                         (fst (CSUC_adapt f fL)) leab
      <= IntegralCSUC f fL.
Proof.
  intros. unfold IntegralCSUC, TotalizeFunc.
  pose proof (CSUC_connect_support
                (TotalizeFunc (CRcarrier R) f (CSUC_fullDomain f fL)) (CSUC_low f fL)
                (CSUC_high f fL) (CSUC_cont_mod f fL)).
  destruct fL, f; simpl; simpl in H0.
  assert (CRmin a CSUC_low0 <= CRmax b CSUC_high0).
  { apply (CRle_trans _ a). apply CRmin_l.
    apply (CRle_trans _ b _ leab). apply CRmax_l. }
  apply (CRle_trans
           _ (UC_integral (fun x1 : CRcarrier R => partialApply x1 (CSUC_fullDomain0 x1))
                          (CRmin a CSUC_low0) (CRmax b CSUC_high0)
                          CSUC_cont_mod0 (fst CSUC_adapt0) H1)).
  apply (UC_integral_extend_nonneg _ CSUC_cont_mod0).
  apply CRmin_l. apply CRmax_l. intros. apply H.
  assert (forall x y:CRcarrier R, x == y -> x <= y).
  { intros. rewrite H2. apply CRle_refl. }
  apply H2. symmetry. apply (UC_integral_extend_zero _ CSUC_cont_mod0).
  apply CRmin_r. apply CRmax_r.
  intros. apply H0. apply CSUC_adapt0. left. apply H3.
  intros. apply H0. apply CSUC_adapt0. right. apply H3.
Qed.

Lemma CSUCIntegralContinuous {R : ConstructiveReals}
  : @ElemIntegralContinuous (@ElemCSUC R) IntegralCSUC.
Proof.
  intros. apply IcontinuousClassic.
  - apply CSUCIntegralHomogeneous.
  - apply CSUCIntegralAdditiveIterate.
  - intros g gL.
    assert (nonNegFunc (PartializeFunc (CRcarrier R) (CSUCUnitTrapeze (CSUC_low g gL) (CSUC_high g gL) 1 (CRzero_lt_one R))))
      as ZnonNeg.
    { intros x xdf. simpl.
      apply (CSUCTrapezeBounded
               (CSUC_low g gL) (CSUC_high g gL)
               1 x (CRzero_lt_one R)).
      apply (CSUC_lowHigh g gL). }
    exists (existT _ (PartializeFunc (CRcarrier R) (CSUCUnitTrapeze (CSUC_low g gL) (CSUC_high g gL) 1 (CRzero_lt_one R)))
              (pair (CSUCTrapeze_IS_CSUC (CSUC_low g gL)
                                         (CSUC_high g gL)
                                         1 (CRzero_lt_one R)
                                         (CSUC_lowHigh g gL))
                    ZnonNeg)).
    intros.
    assert (forall (k : nat) (x : CRcarrier R),
               (0 <= (fun n : nat => TotalizeFunc (CRcarrier R) (fn n) (CSUC_fullDomain (fn n) (fnL n))) k x))
      as fnPos.
    { intros. unfold TotalizeFunc. specialize (H k). clear H0.
      unfold nonNegFunc in H.
      destruct (fnL k), (fn k); simpl; simpl in H. apply H. }
    destruct H0 as [sIfn [icv imaj]].
    assert (forall n : nat,
               (CRabs _
    ((fun k : nat =>
      UC_integral ((fun n0 : nat => TotalizeFunc (CRcarrier R) (fn n0) (CSUC_fullDomain (fn n0) (fnL n0))) k)
        (CSUC_low g gL) (CSUC_high g gL)
        ((fun n0 : nat => CSUC_cont_mod (fn n0) (fnL n0)) k)
        ((fun n0 : nat => fst (CSUC_adapt (fn n0) (fnL n0))) k)
        (CSUC_lowHigh g gL) ) n) <=
  (fun n0 : nat =>
   UC_integral (TotalizeFunc (CRcarrier R) (fn n0) (CSUC_fullDomain (fn n0) (fnL n0)))
     (CSUC_low (fn n0) (fnL n0)) (CSUC_high (fn n0) (fnL n0))
     (CSUC_cont_mod (fn n0) (fnL n0)) (fst (CSUC_adapt (fn n0) (fnL n0)))
     (CSUC_lowHigh (fn n0) (fnL n0))) n)).
    { intro n. rewrite CRabs_right.
      apply CSUC_extend_pos. apply H.
      apply UC_integral_pos.
      intros. specialize (H n). destruct (fnL n), (fn n); simpl. apply H. }
    destruct (series_cv_maj _ _ sIfn H0 icv) as [sIfnTrunc [scv smaj]].
    assert (sIfnTrunc < UC_integral (TotalizeFunc (CRcarrier R) g (CSUC_fullDomain g gL))
                        (CSUC_low g gL) (CSUC_high g gL)
                        (CSUC_cont_mod g gL) (fst (CSUC_adapt g gL))
                        (CSUC_lowHigh g gL) ) as majInt.
    { apply (CRle_lt_trans _ sIfn). apply smaj. exact imaj. }
    destruct (DestructCSUCposPoint
                  R (TotalizeFunc (CRcarrier R) g (CSUC_fullDomain _ gL))
                  (fun n => TotalizeFunc (CRcarrier R) (fn n) (CSUC_fullDomain _ (fnL n)))
                  fnPos (fun n => CSUC_cont_mod _ (fnL n))
                  (fun n => fst (CSUC_adapt _ (fnL n)))
                  (CSUC_cont_mod _ gL)
                  (CSUC_low _ gL) (CSUC_high _ gL) (CSUC_lowHigh _ gL)
                  (CSUC_adapt _ gL) (existT _ sIfnTrunc (pair scv majInt)))
      as [l lcv].
    exists (Build_CommonPointFunSeq
         _ _ g fn l (CSUC_fullDomain g gL l)
         (fun n => CSUC_fullDomain (fn n) (fnL n) l)).
    unfold cpx, cpxF, cpxFn. simpl in lcv.
    split. exists Logic.I. unfold PartializeFunc, partialApply.
    apply CSUCTrapezePlateau. apply lcv. apply lcv.
Qed.

Lemma CSUC_transport_apply
  : forall {R : ConstructiveReals} (f g : PartialFunction (CRcarrier R))
      (fL : Is_CSUC_func f)
      (pEq : PartialFunExtEq f g)
      (x : CRcarrier R),
    TotalizeFunc (CRcarrier R) f (CSUC_fullDomain _ fL) x
    == TotalizeFunc (CRcarrier R) g (CSUC_fullDomain _ (CSUCext f g pEq fL)) x.
Proof.
  intros. destruct pEq, p. apply c.
Qed.

Lemma CSUC_transport_low
  : forall {R : ConstructiveReals} (f g : PartialFunction (CRcarrier R))
      (fL : Is_CSUC_func f)
      (pEq : PartialFunExtEq f g),
    CSUC_low _ fL
    = CSUC_low _ (Lext ElemCSUC f g pEq fL).
Proof.
  intros. destruct pEq, p, f, g, fL; reflexivity.
Qed.

Lemma CSUC_transport_high
  : forall {R : ConstructiveReals} (f g : PartialFunction (CRcarrier R))
      (fL : Is_CSUC_func f)
      (pEq : PartialFunExtEq f g),
    CSUC_high _ fL
    = CSUC_high _ (Lext ElemCSUC f g pEq fL).
Proof.
  intros. destruct pEq, p, f, g, fL; reflexivity.
Qed.

Lemma IntegralCSUC_ext
  : forall {R : ConstructiveReals}
      (g h : PartialFunction (CRcarrier R)) (gCS : Is_CSUC_func g)
      (hCS : Is_CSUC_func h),
    (forall x:CRcarrier R, TotalizeFunc (CRcarrier R) g (CSUC_fullDomain g gCS) x
            == TotalizeFunc (CRcarrier R) h (CSUC_fullDomain h hCS) x)
    -> IntegralCSUC g gCS == IntegralCSUC h hCS.
Proof.
  intros.
  pose proof (CSUC_connect_support
                (TotalizeFunc (CRcarrier R) g (CSUC_fullDomain g gCS)) (CSUC_low g gCS)
                (CSUC_high g gCS) (CSUC_cont_mod g gCS)).
  pose proof (CSUC_connect_support
                (TotalizeFunc (CRcarrier R) h (CSUC_fullDomain h hCS)) (CSUC_low h hCS)
                (CSUC_high h hCS) (CSUC_cont_mod h hCS)).
  unfold IntegralCSUC; destruct gCS, hCS, g, h; simpl; simpl in H, H0, H1.
  unfold TotalizeFunc.
  assert (CRmin CSUC_low0 CSUC_low1 <= CRmax CSUC_high0 CSUC_high1).
  { apply (CRle_trans _ CSUC_low0). apply CRmin_l.
    apply (CRle_trans _ CSUC_high0). apply CSUC_lowHigh0.
    apply CRmax_l. }
  (* Extend bounds *)
  transitivity (UC_integral
                        (fun x2 : CRcarrier R => partialApply x2 (CSUC_fullDomain0 x2))
                        (CRmin CSUC_low0 CSUC_low1)
                        (CRmax CSUC_high0 CSUC_high1) CSUC_cont_mod0 (fst CSUC_adapt0) H2).
  - apply (UC_integral_extend_zero _ CSUC_cont_mod0). apply CRmin_l.
    apply CRmax_l. intros. apply H0. apply CSUC_adapt0.
    left. apply H3. intros. apply H0. apply CSUC_adapt0.
    right. apply H3.
  - transitivity (UC_integral
                    (fun x2 : CRcarrier R => partialApply0 x2 (CSUC_fullDomain1 x2))
                    (CRmin CSUC_low0 CSUC_low1)
                    (CRmax CSUC_high0 CSUC_high1)
                    CSUC_cont_mod1 (fst CSUC_adapt1) H2).
    apply UC_integral_extens. intros. apply H.
    symmetry.
    apply (UC_integral_extend_zero _ CSUC_cont_mod1).
    apply CRmin_r. apply CRmax_r.
    intros. apply H1. apply CSUC_adapt1.
    left. apply H3. intros. apply H1. apply CSUC_adapt1.
    right. apply H3.
Qed.

Lemma IntegralCSUC_bounded
  : forall {R : ConstructiveReals} (g : PartialFunction (CRcarrier R))
      (gCS : Is_CSUC_func g)
      (A : CRcarrier R),
    (forall x:CRcarrier R, TotalizeFunc (CRcarrier R) g (CSUC_fullDomain g gCS) x <= A)
    -> IntegralCSUC g gCS <= (A* (CSUC_high g gCS - CSUC_low g gCS)).
Proof.
  intros. rewrite CRmult_comm. unfold Qminus.
  rewrite <- (UC_integral_constant
               _ _ _ A
               _ (UC_constant A) (CSUC_lowHigh g gCS)).
  unfold IntegralCSUC.
  apply (UC_integral_nonneg
           (TotalizeFunc (CRcarrier R) g (CSUC_fullDomain g gCS))
           (fun _ => A)).
  intros. apply H.
  intros. reflexivity.
Qed.

Lemma CSUCIntegralLimit
  : forall {R : ConstructiveReals} (f : PartialFunction (CRcarrier R))
      (fL : Is_CSUC_func f),
        prod (CR_cv _ (fun n => IntegralCSUC (XminConst f (INR n))
                        (@LminIntStable ElemCSUC n f fL))
               (IntegralCSUC f fL))
         (CR_cv _ (fun n => IntegralCSUC (XminConst (Xabs f) (CR_of_Q R (1# Pos.of_nat (S n))))
                          (@LminConstStable ElemCSUC (CR_of_Q R (1# Pos.of_nat (S n))) (Xabs f)
                                         (invSuccRealPositive n)
                                         (LabsStable ElemCSUC f fL)))
                 0).
Proof.
  split.
  - destruct (CSUC_bounded (TotalizeFunc (CRcarrier R) f (CSUC_fullDomain _ fL))
                           (CSUC_low _ fL) (CSUC_high _ fL)
                           (CSUC_cont_mod _ fL) (CSUC_adapt _ fL)
                           (CSUC_lowHigh _ fL))
      as [B Bmaj].
    destruct (CRup_nat B) as [k kmaj].
    apply (CR_cv_shift _ k).
    apply (CR_cv_eq _ (fun n : nat => IntegralCSUC f fL)).
    intro n.
    apply IntegralCSUC_ext. intro x0.
    assert (PartialFunExtEq
              f (XminConst f (INR (n + k)))) as feq.
    { split. split.
      intros x H. destruct f; simpl. exact H.
      intros x H. destruct f; simpl. exact H.
      intros. unfold XminConst, Xop, partialApply.
      rewrite CRmin_left. rewrite (DomainProp f x1 xD xG).
      reflexivity.
      apply (CRle_trans _ B).
      specialize (Bmaj x1). unfold TotalizeFunc in Bmaj.
      rewrite (DomainProp _ _ _ (CSUC_fullDomain f fL x1)).
      apply (CRle_trans _ _ _ (CRle_abs _)).
      apply CRlt_asym, Bmaj.
      apply (CRle_trans _ (INR k)). apply CRlt_asym, kmaj.
      apply CR_of_Q_le. unfold Qle, Qden, Qnum.
      do 2 rewrite Z.mul_1_r.
      rewrite <- (Z.add_0_r (Z.of_nat k)).
      rewrite Nat2Z.inj_add. rewrite (Z.add_comm (Z.of_nat n)).
      apply Z.add_le_mono_l. apply Nat2Z.is_nonneg. }
    rewrite (CSUC_transport_apply
               f (XminConst f (INR (n + k))) fL feq).
    unfold TotalizeFunc. apply DomainProp.
    exists O. intros. unfold CRminus. rewrite CRplus_opp_r.
    rewrite CRabs_right. rewrite <- CR_of_Q_zero. apply CR_of_Q_le; discriminate.
    apply CRle_refl.
  - intros p.
    destruct (CRup_nat ((CSUC_high f fL - CSUC_low f fL )
                                * (CR_of_Q R (Z.pos p # 1)))) as [k kmaj].
    exists k. intros n H. unfold CRminus. rewrite CRopp_0. rewrite CRplus_0_r.
    rewrite CRabs_right.
    apply (CRle_trans
             _ (CR_of_Q R (1# Pos.of_nat (S n))
                * (CSUC_high _ (@LminConstStable ElemCSUC (CR_of_Q R (1# Pos.of_nat (S n)))
                                                       (Xabs f) (invSuccRealPositive n)
                                              (LabsStable ElemCSUC f fL))
                   - CSUC_low _ (@LminConstStable ElemCSUC (CR_of_Q R (1# Pos.of_nat (S n))) (Xabs f) (invSuccRealPositive n)
                                               (LabsStable ElemCSUC f fL))))).
    + apply IntegralCSUC_bounded.
      intro x0. apply CRmin_r.
    + apply (CRmult_lt_compat_r (CR_of_Q R (1 # p))) in kmaj.
      rewrite CRmult_assoc, <- CR_of_Q_mult in kmaj.
      setoid_replace ((Z.pos p # 1) * (1 # p))%Q with 1%Q in kmaj.
      rewrite CR_of_Q_one, CRmult_1_r in kmaj.
      apply (CRmult_le_reg_l (CR_of_Q R (Z.of_nat (S n) #1))).
      apply CR_of_Q_pos; reflexivity.
      rewrite <- CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((Z.of_nat (S n) # 1) * (1 # Pos.of_nat (S n)))%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_l.
      apply (CRle_trans _ (INR k * CR_of_Q R (1#p))).
      apply (CRle_trans _ (CSUC_high f fL - CSUC_low f fL)).
      2: apply CRlt_asym, kmaj.
      unfold LminConstStable. rewrite <- CSUC_transport_low.
      rewrite <- CSUC_transport_high. destruct f, fL; apply CRle_refl.
      apply CRmult_le_compat_r.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le; discriminate.
      apply CR_of_Q_le. unfold Qle, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, le_S, H.
      unfold Qmult, Qeq, Qnum, Qden.
      rewrite Z.mul_1_r, Z.mul_1_r, Z.mul_1_l, Pos.mul_1_l.
      rewrite <- positive_nat_Z, Nat2Pos.id. reflexivity. discriminate.
      unfold Qmult, Qeq, Qnum, Qden.
      rewrite Z.mul_1_r, Z.mul_1_r, Z.mul_1_l, Pos.mul_1_l. reflexivity.
      apply CR_of_Q_pos; reflexivity.
    + unfold IntegralCSUC.
      apply (UC_integral_pos
               (TotalizeFunc (CRcarrier R)
       (XminConst (Xabs f) (CR_of_Q R (1 # Pos.of_nat (S n))))
       (CSUC_fullDomain
          (XminConst (Xabs f) (CR_of_Q R (1 # Pos.of_nat (S n))))
          (@LminConstStable ElemCSUC (CR_of_Q R (1 # Pos.of_nat (S n)))
             (Xabs f) (invSuccRealPositive n) (LabsStable ElemCSUC f fL))))).
      intros. unfold TotalizeFunc.
      assert (Domain (Xabs f) x0).
      { destruct fL,f; apply CSUC_fullDomain0. }
      rewrite applyXminConst. apply CRmin_glb.
      2: rewrite <- CR_of_Q_zero; apply CR_of_Q_le; discriminate.
      destruct f; apply CRabs_pos.
Qed.

Lemma OneCSUC_IS_CSUC :
  forall {R : ConstructiveReals},
    Is_CSUC_func (PartializeFunc (CRcarrier R)
                                 (CSUCUnitTrapeze 0 0 1 (CRzero_lt_one R))).
Proof.
  intro R. assert (-(1) <= CRone R).
  { apply (CRle_trans _ (-0)).
    apply CRopp_ge_le_contravar, CRlt_asym, CRzero_lt_one.
    rewrite CRopp_0. apply CRlt_asym, CRzero_lt_one. }
  apply (Build_Is_CSUC_func
           R (PartializeFunc (CRcarrier R) (CSUCUnitTrapeze 0 0 1 (CRzero_lt_one R)))
           (fun x:CRcarrier R => Logic.I)
           (-(1)) 1 H (fun eps epsPos => eps *CR_of_Q R (1#2))).
  pose proof (CSUCTrapeze_CSUC 0 0 1 (CRzero_lt_one R) (CRle_refl 0)).
  destruct H0. destruct u. split. split.
  intros. specialize (c0 x0 xPos). rewrite CRmult_1_r in c0. exact c0.
  intros. apply (c1 eps x0 y0 epsPos). rewrite CRmult_1_r. exact H0.
  intros. apply c. destruct H0.
  left. unfold CRminus. rewrite CRplus_0_l. exact c2.
  right. unfold CRminus. rewrite CRplus_0_l. exact c2.
Defined.

Lemma IntegralOneCSUC
  : forall {R : ConstructiveReals},
    IntegralCSUC (PartializeFunc (CRcarrier R) (CSUCUnitTrapeze 0 0 1 (CRzero_lt_one R)))
                 OneCSUC_IS_CSUC == 1.
Proof.
  intro R.
  transitivity (CRone R + 0 - 0).
  rewrite <- (CSUCUnitTrapezeInt 0 0 1 (CRzero_lt_one R) (CRle_refl 0)).
  (* IntegralCSUC is between CR_of_Q (-1) and CR_of_Q 1 *)
  assert (-(1) <= CRone R).
  { apply (CRle_trans _ (-0)).
    apply CRopp_ge_le_contravar, CRlt_asym, CRzero_lt_one.
    rewrite CRopp_0. apply CRlt_asym, CRzero_lt_one. }
  rewrite (UC_integral_bound_proper
             (CSUCUnitTrapeze 0 0 1 (CRzero_lt_one R))
             (0-1) (0+1) (-(1)) 1 _ _ _ H).
  apply UC_integral_extens. reflexivity.
  unfold CRminus. rewrite CRplus_0_l, <- CR_of_Q_one, <- CR_of_Q_opp.
  apply CR_of_Q_morph. reflexivity.
  rewrite CRplus_0_l. reflexivity.
  unfold CRminus. rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r. reflexivity.
Qed.

Definition IntSpaceCSUCFunctions {R : ConstructiveReals} : IntegrationSpace
  := Build_IntegrationSpace ElemCSUC
                            IntegralCSUC
                            CSUCIntegralAdditive
                            CSUCIntegralHomogeneous
                            (PartializeFunc (CRcarrier R) (CSUCUnitTrapeze 0 0 1 (CRzero_lt_one R)))
                            OneCSUC_IS_CSUC
                            IntegralOneCSUC
                            CSUCIntegralContinuous
                            CSUCIntegralLimit.

(* An integrable function for the Lebesgue measure is proper almost everywhere. *)
Lemma CSUCIntegrableProper
  : forall {R : ConstructiveReals} (fn : nat -> PartialFunction (CRcarrier R))
      (x y : CRcarrier R)
      (xD : Domain (XinfiniteSumAbs fn) x)
      (yD : Domain (XinfiniteSumAbs fn) y),
    (forall n : nat, Is_CSUC_func (fn n))
    -> x == y
    -> partialApply _ x xD == partialApply _ y yD.
Proof.
  intros. simpl.
  destruct xD, yD. simpl in c, c0.
  apply series_cv_abs_eq.
  apply (series_cv_eq (fun n : nat => partialApply (fn n) x0 (x1 n))).
  2: apply series_cv_abs_cv.
  intro n. specialize (H n). destruct H, CSUC_adapt0.
  pose proof (UniformContProper _ _ u x0 y0 H0).
  unfold TotalizeFunc in H. transitivity (partialApply (fn n) x0 (CSUC_fullDomain0 x0)).
  apply DomainProp. rewrite H. apply DomainProp.
Qed.

Lemma OpenIntervalIntegrable
  : forall {R : ConstructiveReals} (a b : CRcarrier R),
    a < b
    -> { limInt : @IntegrableSet IntSpaceCSUCFunctions
                                (fun x => CRltProp R a x
                                       /\ CRltProp R x b)
      | MeasureSet limInt == b-a }.
Proof.
  intros.
  assert (forall n:nat, 0 < (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2))) as etaPos.
  { intro n. apply CRmult_lt_0_compat.
    rewrite <- (CRplus_opp_r a). apply CRplus_lt_compat_r, H.
    apply CR_of_Q_pos. reflexivity. }
  pose (fun n:nat => PartializeFunc
                    (CRcarrier R)
                    (CSUCUnitTrapeze (a + (b-a) * CR_of_Q R (1#Pos.of_nat (n+2)))
                                     (b - (b-a) * CR_of_Q R (1#Pos.of_nat (n+2)))
                                     ((b-a) * CR_of_Q R (1#Pos.of_nat (n+2)))
                                     (etaPos n)))
    as fn.
  assert (forall c d : CRcarrier R,
             CR_cv R (fun n => c + d * CR_of_Q R (1 # Pos.of_nat (n + 2))) c)
    as affineCv.
  { intros. apply (CR_cv_proper _ (c+0) c).
    apply CR_cv_plus. apply CR_cv_const. apply (CR_cv_proper _ (0*d)).
    apply (CR_cv_eq _ (fun n : nat => CR_of_Q R (1 # Pos.of_nat (n + 2)) * d)).
    intro n. apply CRmult_comm. apply CR_cv_scale.
    intro p. exists (Pos.to_nat p). intros. unfold CRminus.
    rewrite CRopp_0, CRplus_0_r. rewrite CRabs_right.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply (le_trans _ _ _ H0). rewrite Nat.add_comm.
    apply le_S, le_S, le_refl. intro abs. rewrite Nat.add_comm in abs. discriminate.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    rewrite CRmult_0_l. reflexivity. rewrite CRplus_0_r. reflexivity. }
  assert (CR_cv R (fun n => a + (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2))) a)
    as cv_left.
  { apply affineCv. }
  assert (CR_cv R (fun n => b - (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2))) b)
    as cv_right.
  { apply (CR_cv_eq _ (fun n => b + (-(b - a)) * CR_of_Q R (1 # Pos.of_nat (n + 2)))).
    intro n. apply CRplus_morph. reflexivity.
    rewrite CRopp_mult_distr_l. reflexivity.
    apply affineCv. }
  assert (forall x (xdn : forall n, Domain (fn n) x),
             (CRltProp R a x /\ CRltProp R x b)
             -> CR_cv R (fun n => partialApply (fn n) x (xdn n)) 1) as inPlateau.
  (* Serves twice. First, for the domain inclusion when the limit is below 1,
     we assume by contradiction that the point is in the interval, and then 1
     is below 1. Second, to prove the partial restriction inside the interval. *)
  { intros. destruct H0.
    apply CRltEpsilon in H0. apply CRltEpsilon in H1.
    destruct (CR_cv_open_above _ x0 a cv_left H0).
    destruct (CR_cv_open_below _ x0 b cv_right H1).
    exists (max x1 x2). intros.
    specialize (c i). specialize (c0 i).
    simpl. rewrite CSUCTrapezePlateau. unfold CRminus.
    rewrite CRplus_opp_r, CRabs_right. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate. apply CRle_refl.
    split; apply CRlt_asym. apply c. apply (le_trans _ (max x1 x2)).
    apply Nat.le_max_l. exact H2. apply c0.
    apply (le_trans _ (max x1 x2)). apply Nat.le_max_r. exact H2. }

  assert (forall n:nat, a + (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2))
                 <= b - (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2))) as fnL.
  { intro n.
    apply (CRplus_le_reg_r ((b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2)))).
    unfold CRminus. rewrite (CRplus_assoc b), CRplus_opp_l, CRplus_0_r.
    apply (CRplus_le_reg_l (-a)). rewrite <- CRplus_assoc, <- CRplus_assoc.
    rewrite CRplus_opp_l, CRplus_0_l.
    rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus.
    rewrite Qinv_plus_distr, CRplus_comm.
    rewrite <- (CRmult_1_r (-a + b)).
    rewrite CRmult_assoc. apply CRmult_le_compat_l.
    rewrite <- (CRplus_opp_l a). apply CRplus_le_compat_l, CRlt_asym, H.
    rewrite CRmult_1_l.
    rewrite <- CR_of_Q_one. apply CR_of_Q_le.
    unfold Qle,Qnum,Qden. rewrite Z.mul_1_r, Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. rewrite Nat.add_comm. apply le_n_S, le_n_S, le_0_n.
    intro abs. rewrite Nat.add_comm in abs. discriminate. }

  assert (PartialRestriction (XpointwiseLimit fn)
                             (CharacFunc (fun x0 : CRcarrier R =>
                                            CRltProp R a x0
                                            /\ CRltProp R x0 b))).
  { split.
    - intros x xdf. simpl. destruct xdf as [xdn c].
      apply CR_complete in c. destruct c as [l lcv].
      destruct (CRltLinear R). destruct (s 0 l 1 (CRzero_lt_one R)).
      + left.
        apply (CR_cv_open_below _ 0) in lcv. 2: exact c.
        destruct lcv as [n nmaj].
        specialize (nmaj n (le_refl n)).
        apply (CSUCTrapezeInPlateau
                 (a + (b-a) * CR_of_Q R (1#Pos.of_nat (n+2)))
                 (b - (b-a) * CR_of_Q R (1#Pos.of_nat (n+2)))
                 ((b-a) * CR_of_Q R (1#Pos.of_nat (n+2))) x
                 (etaPos n)) in nmaj.
        destruct nmaj. split.
        apply CRltForget.
        unfold CRminus in c0.
        rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r in c0.
        exact c0.
        unfold CRminus in c1.
        rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r in c1.
        apply CRltForget. exact c1.
      + right. intro abs. specialize (inPlateau x xdn abs).
        rewrite (CR_cv_unique _ _ _ inPlateau lcv) in c.
        exact (CRlt_asym l l c c).
    - intros. simpl in xG. destruct xG.
      + (* one *)
        apply applyPointwiseLimit.
        exact (inPlateau _ (fun n => let (xdn,_) := xD in xdn n) a0).
      + (* zero *)
        apply applyPointwiseLimit.
        apply (CR_cv_eq _ (fun _ => 0)). 2: apply CR_cv_const.
        intros. simpl.
        unfold CSUCUnitTrapeze, UCUnitHeaviside.
        rewrite (CRinv_morph _ ((b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)))
                             _ (inr (etaPos n0))).
        rewrite (CRinv_morph (b - (b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)) +
           (b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)) -
           (b - (b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2))))
                             ((b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)))
                             _ (inr (etaPos n0))).
        destruct (CRltLinear R).
        destruct (s a x0 b H).
        assert (b <= x0).
        { intro abs. apply n. split. apply CRltForget, c. apply CRltForget, abs. }
        clear c. rewrite CRmin_left, CRmin_left.
        rewrite CRmax_right. unfold CRminus. rewrite CRplus_opp_r. reflexivity.
        apply CRlt_asym, CRzero_lt_one.
        apply (CRmult_le_reg_r ((b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)))).
        apply etaPos. rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_1_l.
        unfold CRminus.
        rewrite <- CRplus_0_l.
        rewrite CRopp_plus_distr, CRopp_involutive.
        do 2 rewrite <- CRplus_assoc. apply CRplus_le_compat_r.
        rewrite CRplus_0_r.
        rewrite <- (CRplus_opp_r b). apply CRplus_le_compat_r, H0.
        apply (CRmult_le_reg_r ((b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)))).
        apply etaPos. rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_1_l.
        unfold CRminus.
        rewrite CRopp_plus_distr, CRopp_involutive, <- CRplus_0_l.
        rewrite <- CRplus_assoc, <- CRplus_assoc. apply CRplus_le_compat_r.
        rewrite CRplus_0_r, CRplus_0_l.
        rewrite <- (CRplus_opp_r (a + (b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)))).
        apply CRplus_le_compat_r, (CRle_trans _ b).
        2: exact H0. apply (CRplus_le_reg_l (-a)).
        rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
        rewrite <- (CRmult_1_r (-a+b)), (CRplus_comm (-a)).
        apply CRmult_le_compat_l.
        rewrite <- (CRplus_opp_r a). apply CRplus_le_compat_r. apply CRlt_asym, H.
        rewrite <- CR_of_Q_one. apply CR_of_Q_le.
        unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_l.
        apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
        rewrite Nat2Pos.id. rewrite Nat.add_comm. apply le_n_S, le_0_n.
        intro abs. rewrite Nat.add_comm in abs. discriminate.
        assert (x0 <= a).
        { intro abs. apply n. split. apply CRltForget, abs. apply CRltForget, c. }
        clear c. rewrite CRmax_left, CRmax_left.
        unfold CRminus. rewrite CRplus_opp_r. reflexivity.
        apply (CRle_trans _ _ _ (CRmin_r _ _)).
        apply (CRmult_le_reg_r ((b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)))).
        apply etaPos. rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r.
        rewrite <- (CRplus_opp_r (b - (b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)))).
        apply CRplus_le_compat_r. apply (CRle_trans _ _ _ H0).
        apply (CRplus_le_reg_l (-b)). unfold CRminus.
        rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
        setoid_replace (-b+a) with (-(b-a)). apply CRopp_ge_le_contravar.
        rewrite <- (CRmult_1_r (b-a)).
        apply CRmult_le_compat_l. rewrite <- (CRplus_opp_r a).
        apply CRplus_le_compat_r, CRlt_asym, H.
        rewrite <- CR_of_Q_one. apply CR_of_Q_le.
        unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_l.
        apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
        rewrite Nat2Pos.id. rewrite Nat.add_comm. apply le_n_S, le_0_n.
        intro abs. rewrite Nat.add_comm in abs. discriminate.
        unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive. reflexivity.
        apply (CRle_trans _ _ _ (CRmin_r _ _)).
        apply (CRmult_le_reg_r ((b - a) * CR_of_Q R (1 # Pos.of_nat (n0 + 2)))).
        apply etaPos. rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r.
        unfold CRminus. rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
        rewrite <- (CRplus_opp_r a). apply CRplus_le_compat_r, H0.
        unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
        reflexivity.
        unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive.
        rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l. reflexivity.
  }
  destruct (IntegralMonotoneConvergence
              IntSpaceCSUCFunctions
              fn (fun n => @IntegrableL IntSpaceCSUCFunctions
               (fn n) (CSUCTrapeze_IS_CSUC
             (a + (b-a) * CR_of_Q R (1#Pos.of_nat (n+2)))
             (b - (b-a) * CR_of_Q R (1#Pos.of_nat (n+2)))
             ((b-a) * CR_of_Q R (1#Pos.of_nat (n+2))) (etaPos n) (fnL n)))
              (b-a))
    as [limInt mesRect].
  - intros n x xdf xdg.
    unfold fn, PartializeFunc, partialApply.
    apply TrapezeIncluded.
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    reflexivity. unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    reflexivity. apply CRmult_le_compat_l.
    apply CRle_minus, CRlt_asym, H.
    apply CR_of_Q_le.
    unfold Qle,Qnum,Qden. rewrite Z.mul_1_l, Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id, Nat2Pos.id. apply le_S, le_refl.
    discriminate.
    intro abs. rewrite Nat.add_comm in abs. discriminate.
  - simpl.
    apply (CR_cv_eq _ (fun n => b-a
                             + (-(b-a)) * CR_of_Q R (1 # Pos.of_nat (n + 2)))).
    2: apply affineCv.
    intro n. rewrite IntegralLstable. simpl.
    symmetry. unfold fn.
    unfold IntegralCSUC, CSUCTrapeze_IS_CSUC, CSUC_fullDomain, CSUC_low;
    simpl.
    rewrite (UC_integral_extens
               _ (CSUCUnitTrapeze (a + (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2)))
             (b - (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2)))
             ((b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2))) (etaPos n))
               _ _
               _ (fun eps epsPos => eps * CR_of_Q R (1#2) * ((b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2)))) _
               (CSUCUnitTrapeze_cont _ _ _ _ (fnL n))
               _  (TrapezeLe _ _ _ (etaPos n) (fnL n))).
    2: intros; reflexivity.
    rewrite (CSUCUnitTrapezeInt
               (a + (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2)))
               (b - (b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2)))
               ((b - a) * CR_of_Q R (1 # Pos.of_nat (n + 2)))
               (etaPos n) (fnL n)).
    unfold CRminus.
    rewrite CRplus_comm, CRopp_plus_distr, CRplus_assoc.
    rewrite <- (CRplus_assoc (- ((b + - a) * CR_of_Q R (1 # Pos.of_nat (n + 2))))).
    rewrite CRplus_opp_l, CRplus_0_l, <- CRplus_assoc, (CRplus_comm (-a)).
    rewrite CRopp_mult_distr_l. reflexivity.
  - exists (@IntegrableFunctionExtensional
         IntSpaceCSUCFunctions _ _ X limInt).
    unfold MeasureSet. rewrite IntegralRestrict. exact mesRect.
Qed.

Lemma ClosedIntervalIntegrable
  : forall {R : ConstructiveReals} (a b : CRcarrier R),
    a <= b
    -> { limInt : @IntegrableSet IntSpaceCSUCFunctions
                                (fun x => a <= x <= b)
      | MeasureSet limInt == b-a }.
Proof.
  intros.
  assert (forall n:nat, a - CR_of_Q R (1 # Pos.of_nat n)
                 < b + CR_of_Q R (1 # Pos.of_nat n)) as ltabn.
  { intro n. apply (CRle_lt_trans _ (a + 0)).
    rewrite <- CRopp_0. apply CRplus_le_compat_l, CRopp_ge_le_contravar.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    apply (CRle_lt_trans _ (b+0)). apply CRplus_le_compat_r, H.
    apply CRplus_lt_compat_l, CR_of_Q_pos. reflexivity. }
  assert (CR_cv R (fun i : nat => CR_of_Q R (1 # Pos.of_nat i)) 0) as invCv.
  { intro p. exists (Pos.to_nat p).
    intros. unfold CRminus. rewrite CRopp_0, CRplus_0_r, CRabs_right.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le. rewrite Nat2Pos.id.
    exact H0. destruct i. exfalso. inversion H0.
    pose proof (Pos2Nat.is_pos p). rewrite H2 in H1. inversion H1.
    discriminate. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. }
  destruct (@IntegrableSetCountableIntersect
              IntSpaceCSUCFunctions
              (fun n x => CRltProp R (a - CR_of_Q _ (1 # Pos.of_nat n)) x
                       /\ CRltProp R x (b + CR_of_Q _ (1 # Pos.of_nat n)))
              (fun n => let (i,_) := OpenIntervalIntegrable _ _ (ltabn n) in i)
              (b-a)).
  - apply (CR_cv_eq _ (fun n => b + CR_of_Q R (1 # Pos.of_nat n)
                                 - (a - CR_of_Q R (1 # Pos.of_nat n)))).
    intro n. rewrite MeasureIntersectSeqDecr.
    destruct (OpenIntervalIntegrable
                (a - CR_of_Q R (1 # Pos.of_nat n))
                (b + CR_of_Q R (1 # Pos.of_nat n)) (ltabn n)).
    symmetry; exact c. intros.
    destruct H0. split. apply CRltForget.
    apply CRltEpsilon in H0.
    apply (CRle_lt_trans _ (a - CR_of_Q R (1 # Pos.of_nat (S n0)))).
    2: exact H0. apply CRplus_le_compat_l. apply CRopp_ge_le_contravar.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos.
    destruct n0. discriminate.
    apply Pos2Nat.inj_le. rewrite Nat2Pos.id, Nat2Pos.id.
    apply le_S, le_refl. discriminate. discriminate.
    apply CRltEpsilon in H1. apply CRltForget.
    apply (CRlt_le_trans _ _ _ H1).
    apply CRplus_le_compat_l. apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos.
    destruct n0. discriminate.
    apply Pos2Nat.inj_le. rewrite Nat2Pos.id, Nat2Pos.id.
    apply le_S, le_refl. discriminate. discriminate.
    apply CR_cv_minus.
    apply (CR_cv_proper _ (b+0)). apply CR_cv_plus.
    apply CR_cv_const. exact invCv. rewrite CRplus_0_r. reflexivity.
    apply (CR_cv_proper _ (a-0)). apply CR_cv_minus.
    apply CR_cv_const. exact invCv.
    unfold CRminus. rewrite CRopp_0, CRplus_0_r. reflexivity.
  - assert (forall x, (forall n : nat,
          CRltProp R (a - CR_of_Q R (1 # Pos.of_nat n)) x /\
          CRltProp R x (b + CR_of_Q R (1 # Pos.of_nat n)))
                 <-> a <= x <= b).
    { split. intros. split.
      apply (CR_cv_bound_up (fun n => (a - CR_of_Q R (1 # Pos.of_nat n))) _ _ O).
      intros. specialize (H0 n) as [H0 _]. apply CRlt_asym, CRltEpsilon, H0.
      apply (CR_cv_proper _ (a-0)). apply CR_cv_minus.
      apply CR_cv_const. exact invCv.
      unfold CRminus. rewrite CRopp_0, CRplus_0_r. reflexivity.
      apply (CR_cv_bound_down (fun n => (b + CR_of_Q R (1 # Pos.of_nat n))) _ _ O).
      intros. specialize (H0 n) as [_ H0]. apply CRlt_asym, CRltEpsilon, H0.
      apply (CR_cv_proper _ (b+0)). apply CR_cv_plus.
      apply CR_cv_const. exact invCv. rewrite CRplus_0_r. reflexivity.
      intros. split. apply CRltForget.
      apply (CRlt_le_trans _ (a+-0)).
      2: rewrite CRopp_0, CRplus_0_r; exact (proj1 H0).
      apply CRplus_lt_compat_l, CRopp_gt_lt_contravar, CR_of_Q_pos.
      reflexivity.
      apply CRltForget.
      apply (CRle_lt_trans _ (b+0)). rewrite CRplus_0_r. exact (proj2 H0).
      apply CRplus_lt_compat_l, CR_of_Q_pos. reflexivity. }
    exists (IntegrableSetExtensional
         (fun x : X (ElemFunc IntSpaceCSUCFunctions) =>
          forall n : nat,
          CRltProp R (a - CR_of_Q R (1 # Pos.of_nat n)) x /\
          CRltProp R x (b + CR_of_Q R (1 # Pos.of_nat n))) _ H0 x0).
    rewrite <- (MeasureExtensional _ _ x0 _ H0). exact c.
Qed.
