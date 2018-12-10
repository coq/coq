(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(*
  Partial functions between two sets X and Y. They have domains of
  definition which are subsets of X.
 *)

Require Import List.
Require Import QArith.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructiveRcomplete.

Local Open Scope ConstructiveReals.


(*
   The type of real-valued partial functions on X. Partial means the
   functions are defined only on subsets D of X, called their domains.

   In classical logic, partial functions are useless for the theory
   of integration, because a partial function X -> R can be extended
   to all X by zeroes, with the same integral. However, in constructive
   mathematics a function R -> R must be undefined at its points of
   discontinuity.

   Besides, we will prove that the domain of an integrable function
   X -> R has full measure in X, ie it is the complement of a null
   set of X.
 *)
Record PartialFunctionXY {X Y : Set} {Yeq : Y -> Y -> Prop} : Type :=
  {
    Domain : X -> Set;
    partialApply : forall x : X, Domain x -> Y;
    DomainProp : forall (x : X) (p q : Domain x),
        Yeq (partialApply x p) (partialApply x q);
  }.

Definition PartialFunction {R : ConstructiveReals} (X : Set) : Type
  := @PartialFunctionXY X (CRcarrier R) (CReq R).

Definition TotalizeFunc {R : ConstructiveReals} (X : Set)
           (f : PartialFunction X)
           (domainTotal : forall x:X, Domain f x)
  : X -> CRcarrier R
  := fun x => partialApply f x (domainTotal x).

Definition PartializeFunc {R : ConstructiveReals} (X : Set)
           (f : X -> CRcarrier R) : PartialFunction X
  := Build_PartialFunctionXY
       X (CRcarrier R) (CReq R) (fun x:X => True) (fun x _ => f x)
       (fun x _ _ => CReq_refl (f x)).

Record CommonPointFunSeq {R : ConstructiveReals}
       (X : Set) (f : @PartialFunction R X)
       (fn : nat -> @PartialFunction R X) : Set
  := {
      cpx : X;
      cpxF : Domain f cpx;
      cpxFn : forall n:nat, Domain (fn n) cpx;
    }.

(* We have a major use of the sort Set for integration, that could not be
   done with Ensemble X : the domain of the pointwise limit of a
   sequence of functions. The limit is stored at each point in sort Set,
   so that we can form the (partial) limit function. *)
Definition XpointwiseLimit {R : ConstructiveReals}
           {X : Set} (fn : nat -> @PartialFunction R X)
  : @PartialFunction R X.
Proof.
  apply (Build_PartialFunctionXY
           X (CRcarrier R) (CReq R)
           (* x is in all domains and the sequence converges *)
           (fun x:X => { xnlim : (forall n:nat, Domain (fn n) x)
                         & CR_cauchy _ (fun n:nat => partialApply (fn n) x (xnlim n)) })
           (fun x p
            => let (xnlim, cau) := p in
               let (c,d) := CR_complete R _ cau in c)).
  intros. destruct p,q.
  destruct (CR_complete R (fun n : nat => partialApply (fn n) x (x0 n)) c).
  destruct (CR_complete R (fun n : nat => partialApply (fn n) x (x1 n)) c0).
  apply (CR_cv_unique (fun n : nat => partialApply (fn n) x (x0 n))).
  exact c1. apply (CR_cv_eq _ (fun n : nat => partialApply (fn n) x (x1 n))).
  2: exact c2. intro n. apply DomainProp.
Defined.

Lemma applyPointwiseLimit
  : forall {R : ConstructiveReals} {X : Set}
           (fn : nat -> PartialFunction X)
           (x : X)
           (xD : Domain (XpointwiseLimit fn) x)
           (a : CRcarrier R),
    prod (partialApply (XpointwiseLimit fn) x xD == a
          -> CR_cv _ (fun n => partialApply (fn n) x
                                       (let (xn, _) := xD in xn n))
                       a)
         (CR_cv _ (fun n => partialApply (fn n) x
                                       (let (xn, _) := xD in xn n))
                       a
         -> partialApply (XpointwiseLimit fn) x xD == a).
Proof.
  intros. simpl. destruct xD.
  destruct (CR_complete R (fun n : nat => partialApply (fn n) x (x0 n)) c).
  split.
  - intros. exact (CR_cv_proper _ x1 a c0 H).
  - intros.
    apply (CR_cv_unique (fun n : nat => partialApply (fn n) x (x0 n))).
    exact c0. exact H.
Qed.

Definition XinfiniteSumAbs {R : ConstructiveReals} {X : Set}
           (fn : nat -> @PartialFunction R X)
  : @PartialFunction R X.
Proof.
  apply (Build_PartialFunctionXY
           X (CRcarrier R) (CReq R)
           (* x is in all domains and the series converges *)
           (fun x:X => { xnlim : (forall n:nat, Domain (fn n) x)
                         & CR_cauchy _ (CRsum (fun n:nat => CRabs _ (partialApply (fn n) x (xnlim n)))) })
           (fun x p
            => let (xnlim, cau) := p in
               let (c,d) := series_cv_abs _ cau in c)).
  intros. destruct p,q.
  destruct (series_cv_abs (fun n : nat => partialApply (fn n) x (x0 n)) c).
  destruct (series_cv_abs (fun n : nat => partialApply (fn n) x (x1 n)) c0).
  apply (CR_cv_unique (CRsum (fun n : nat => partialApply (fn n) x (x0 n)))).
  exact s. apply (series_cv_eq (fun n : nat => partialApply (fn n) x (x1 n))).
  2: exact s0. intro n. apply DomainProp.
Defined.

Definition domainInfiniteSumAbsInc {R : ConstructiveReals} {X : Set}
           (fn : nat -> PartialFunction X)
           (x : X)
           (xnD : forall n:nat, Domain (fn n) x)
           (lim : CRcarrier R)
  : series_cv (fun n => CRabs _ (partialApply (fn n) x (xnD n))) lim
    -> Domain (XinfiniteSumAbs fn) x.
Proof.
  intros cvlim. exists xnD.
  apply (Rcv_cauchy_mod _ lim cvlim).
Qed.

Definition domainInfiniteSumAbsIncReverse
           {R : ConstructiveReals} {X : Set} (fn : nat -> @PartialFunction R X) (x : X)
  : Domain (XinfiniteSumAbs fn) x
    -> forall n:nat, Domain (fn n) x
  := fun xD n => let (xn, _) := xD in xn n.

Lemma applyInfiniteSumAbs
  : forall {R : ConstructiveReals} (X : Set)
           (fn : nat -> PartialFunction X)
           (x : X)
           (xD : Domain (XinfiniteSumAbs fn) x)
           (a : CRcarrier R),
    prod (partialApply (XinfiniteSumAbs fn) x xD == a
          -> series_cv (fun n => partialApply (fn n) x
                                       (domainInfiniteSumAbsIncReverse fn x xD n))
                   a)
         (series_cv (fun n => partialApply (fn n) x
                                       (domainInfiniteSumAbsIncReverse fn x xD n))
                       a
         -> partialApply (XinfiniteSumAbs fn) x xD == a).
Proof.
  intros. unfold domainInfiniteSumAbsIncReverse.
  destruct xD. simpl.
  destruct (series_cv_abs (fun n : nat => partialApply (fn n) x (x0 n))).
  split.
  - intros. exact (CR_cv_proper _ _ _ s H).
  - intros.
    apply (series_cv_unique (fun n : nat => partialApply (fn n) x (x0 n))); assumption.
Qed.

Definition DomainInclusion {R : ConstructiveReals} {X : Set}
           (f g : @PartialFunction R X)
  : Set (* Prop-like *)
  := forall x:X, Domain f x -> Domain g x.

Definition PartialRestriction {R : ConstructiveReals} {X : Set}
           (f g : @PartialFunction R X) : Type
  := prod (DomainInclusion f g)
          (forall (x : X) (xD : Domain f x) (xG : Domain g x),
              partialApply f x xD == partialApply g x xG).

Definition PartialRestriction_refl
  : forall {R : ConstructiveReals} (X : Set) (f : @PartialFunction R X),
    PartialRestriction f f.
Proof.
  split.
  - exact (fun x a => a).
  - intros. apply DomainProp.
Qed.

Definition PartialRestriction_trans
  : forall {R : ConstructiveReals} (X : Set) (f g h : @PartialFunction R X),
    PartialRestriction f g
    -> PartialRestriction g h
    -> PartialRestriction f h.
Proof.
  intros R X f g h H H0. split.
  - intros x H1. apply H0, H, H1.
  - intros. destruct H, H0. rewrite <- (c0 x (d x xD)), <- (c x xD).
    reflexivity.
Qed.

Definition PartialFunExtEq {R : ConstructiveReals} {X : Set}
           (f g : @PartialFunction R X) : Set
  := (DomainInclusion f g)
     * (DomainInclusion g f)
     * (forall (x : X) (xD : Domain f x) (xG : Domain g x),
           partialApply f x xD == partialApply g x xG).

Definition Xconst {R : ConstructiveReals} (X : Set) (c : CRcarrier R)
  : PartialFunction X
  := Build_PartialFunctionXY
       X (CRcarrier R) (CReq R) (fun x => True) (fun x _ => c)
       (fun _ _ _ => CReq_refl c).

Definition XopXY (X Y : Set) (Yeq : Y -> Y -> Prop)
           (f : @PartialFunctionXY X Y Yeq) (op : Y -> Y)
  : (forall x y : Y, Yeq x y -> Yeq (op x) (op y))
    -> @PartialFunctionXY X Y Yeq
  := fun H => Build_PartialFunctionXY
             X Y Yeq (Domain f) (fun x p => op (partialApply f x p))
             (fun x p q => H _ _ (DomainProp f x p q)).

Definition Xop {R : ConstructiveReals} (X : Set) (f : PartialFunction X)
           (op : CRcarrier R -> CRcarrier R)
  : (forall x y : CRcarrier R, x == y -> op x == op y)
    -> PartialFunction X
  := fun H => Build_PartialFunctionXY
             X (CRcarrier R) (CReq R) (Domain f) (fun x p => op (partialApply f x p))
             (fun x p q => H _ _ (DomainProp f x p q)).

Definition Xabs {R : ConstructiveReals} {X : Set} (f : @PartialFunction R X)
  : @PartialFunction R X
  := Xop X f (CRabs R) (CRabs_morph_prop R).

Lemma applyXabs : forall {R : ConstructiveReals} {X : Set}
                    (f : PartialFunction X)
                    (x : X)
                    (xD : Domain f x),
    partialApply (Xabs f) x xD
    = CRabs R (partialApply f x xD).
Proof.
  reflexivity.
Qed.

Definition Xscale {R : ConstructiveReals} {X : Set} (a : CRcarrier R)
           (f : PartialFunction X) : PartialFunction X
  := Xop X f (fun x => a * x)
         (CRmult_morph R a a (CReq_refl a)).

Lemma applyXscale : forall {R : ConstructiveReals} {X : Set}
                      (f : PartialFunction X)
                      (a : CRcarrier R)
                      (x : X)
                      (xD : Domain f x),
    partialApply (Xscale a f) x xD
    = a * (partialApply f x xD).
Proof.
  reflexivity.
Qed.

(* To intersect the domains of a sequence of functions,
   we build the zero function on that intersection. *)
Definition Domain_intersect_countable {R : ConstructiveReals} {X : Set}
           (fn : nat -> @PartialFunction R X)
  : PartialFunction X
  := XinfiniteSumAbs(fun n => Xscale 0 (fn n)).


Definition XbinOpXY (X Y : Set) (Yeq : Y -> Y -> Prop)
           (f g : @PartialFunctionXY X Y Yeq) (op : Y -> Y -> Y)
  : (forall x y z t : Y, Yeq x y -> Yeq z t -> Yeq (op x z) (op y t))
    -> @PartialFunctionXY X Y Yeq.
Proof.
  intros.
  apply (Build_PartialFunctionXY
           X Y Yeq
           (fun x => prod (Domain f x) (Domain g x))
           (fun x xD => let (a,b) := xD in op (partialApply f x a) (partialApply g x b))).
  intros. destruct p,q. apply H.
  - apply DomainProp.
  - apply DomainProp.
Defined.

Definition XbinOp {R : ConstructiveReals} {X : Set} (f g : PartialFunction X)
           (op : CRcarrier R -> CRcarrier R -> CRcarrier R)
           (opEq : forall x y z t : CRcarrier R, x == y -> z == t -> op x z == op y t)
  : PartialFunction X
  := XbinOpXY X (CRcarrier R) (CReq R) f g op opEq.

(* This definition of the sum of partial functions will have
   a major consequence on measure theory : all integrable
   functions are defined almost everywhere. Otherwise the
   intersection of domains could reduce the integral of the
   sum of 2 functions. For example, if an integrable function
   has R+ for domain, then the measure of R- is zero. *)
Definition Xplus {R : ConstructiveReals} {X : Set} (f g : PartialFunction X)
  : PartialFunction X
  := XbinOp f g (CRplus R)
            (fun x y z t Hxy => CRplus_morph R x y Hxy z t).

Lemma applyXplus : forall {R : ConstructiveReals} {X : Set}
                     (f g : @PartialFunction R X)
                     (x : X)
                     (xdf : Domain f x)
                     (xdg : Domain g x),
    partialApply (Xplus f g) x (pair xdf xdg)
    == partialApply f x xdf + partialApply g x xdg.
Proof.
  reflexivity.
Qed.

Definition Xminus {R : ConstructiveReals} {X : Set}
           (f g : PartialFunction X) : PartialFunction X
  := Xplus f (Xscale (CRopp R 1) g).

Lemma applyXminus : forall {R : ConstructiveReals} {X : Set}
                      (f g : @PartialFunction R X)
                      (x : X)
                      (xdf : Domain f x)
                      (xdg : Domain g x),
    partialApply (Xminus f g) x (pair xdf xdg)
    == partialApply f x xdf - partialApply g x xdg.
Proof.
  intros. apply CRplus_morph. reflexivity.
  rewrite applyXscale. rewrite <- CRopp_mult_distr_l.
  rewrite CRmult_1_l. reflexivity.
Qed.

Definition Xmult {R : ConstructiveReals} {X : Set}
           (f g : PartialFunction X) : PartialFunction X
  := XbinOp f g (CRmult R)
            (fun x y z t Hxy => CRmult_morph R x y Hxy z t).

Lemma applyXmult : forall {R : ConstructiveReals} {X : Set}
                     (f g : @PartialFunction R X)
                     (x : X)
                     (xdf : Domain f x)
                     (xdg : Domain g x),
    partialApply (Xmult f g) x (pair xdf xdg)
    == partialApply f x xdf * partialApply g x xdg.
Proof.
  reflexivity.
Qed.

Definition XminConst {R : ConstructiveReals} {X : Set}
           (f : @PartialFunction R X) (a : CRcarrier R) : PartialFunction X
  := Xop X f (fun x => CRmin x a)
         (fun x y Hxy => CRmin_morph _ x y Hxy a a (CReq_refl a)).

Lemma applyXminConst : forall {R : ConstructiveReals} {X : Set}
                         (f : PartialFunction X)
                         (a : CRcarrier R)
                         (x : X)
                         (xD : Domain f x),
    partialApply (XminConst f a) x xD
    = CRmin (partialApply f x xD) a.
Proof.
  reflexivity.
Qed.

Definition XmaxConst {R : ConstructiveReals} {X : Set}
           (f : @PartialFunction R X) (a : CRcarrier R) : PartialFunction X
  := Xop X f (fun x => CRmax x a)
         (fun x y Hxy => CRmax_morph _ x y Hxy a a (CReq_refl a)).


(* This definition is biased in favor of integrable functions,
   ie functions defined almost everywhere.
   Literally it means that f <= g on the intersection of their domains. *)
Definition partialFuncLe {R : ConstructiveReals} {X : Set}
           (f g : @PartialFunction R X) : Prop
  := forall (x : X) (xdf : Domain f x) (xdg : Domain g x),
    partialApply f x xdf <= partialApply g x xdg.

Definition nonNegFunc {R : ConstructiveReals} {X : Set}
           (f : @PartialFunction R X) : Prop
  := forall (x : X) (xdf : Domain f x), 0 <= partialApply f x xdf.

Lemma zeroNonNeg : forall {R : ConstructiveReals},
    nonNegFunc (@Xconst R (CRcarrier R) 0).
Proof.
  intros R x xdf. apply CRle_refl.
Qed.

Lemma nonNegFuncPlus {R : ConstructiveReals} {X : Set}
      (f g : @PartialFunction R X)
  : nonNegFunc f
    -> nonNegFunc g
    -> nonNegFunc (Xplus f g).
Proof.
  intros H H0 x xdf. destruct xdf; simpl.
  apply (CRle_trans _ (partialApply f x d + 0)).
  rewrite CRplus_0_r. apply H. apply CRplus_le_compat_l.
  apply H0.
Qed.

Fixpoint Xsum {R : ConstructiveReals} {X : Set}
         (fn : nat -> PartialFunction X) (n : nat)
  : @PartialFunction R X :=
  match n with
  | O => fn O
  | S i => (Xplus (Xsum fn i) (fn (S i)))
  end.

Definition XsumList {R : ConstructiveReals} {X : Set}
  : list (@PartialFunction R X) -> PartialFunction X
  := fold_right Xplus
                (* empty list means zero function defined everywhere *)
                (Xconst _ 0).

Lemma nonNegSumFunc {R : ConstructiveReals} {X : Set}
      (fn : nat -> @PartialFunction R X)
  : (forall n:nat, nonNegFunc (fn n))
    -> (forall n:nat, nonNegFunc (Xsum fn n)).
Proof.
  intros. induction n.
  - intros x. simpl. apply H.
  - intros x. simpl. apply nonNegFuncPlus. assumption. apply H.
Qed.

Lemma Nat_le_succ_r_dec : forall n m : nat,
    le n (S m) -> { le n m } + { n = S m }.
Proof.
  intros. destruct (Nat.eq_dec n (S m)). right. assumption.
  left. destruct (Nat.le_succ_r n m) as [H0 _]. destruct H0.
  assumption. assumption. contradiction.
Qed.

Definition domainXsumInc {R : ConstructiveReals} {X : Set}
           (fn : nat -> @PartialFunction R X)
           (x : X)
           (xn : forall n:nat, Domain (fn n) x)
  : forall n:nat, Domain (Xsum fn n) x.
Proof.
  induction n.
  - exact (xn O).
  - simpl. split. apply IHn. apply xn.
Qed.

Definition domainXsumIncReverse
  : forall {R : ConstructiveReals} {X : Set}
      (fn : nat -> @PartialFunction R X)
      (k n : nat)
      (x : X)
      (xD : Domain (Xsum fn n) x),
    le k n -> Domain (fn k) x.
Proof.
  induction n.
  - intros. replace k with O. exact xD.
    inversion H. reflexivity.
  - intros. apply Nat_le_succ_r_dec in H. simpl in xD. destruct H.
    + specialize (IHn x (fst xD) l).
      exact IHn.
    + subst k. exact (snd xD).
Qed.

(* Simplification of the previous lemma to avoid proof irrelevance. *)
Definition domainXsumIncLast
  : forall {X : Set} {R : ConstructiveReals}
      (fn : nat -> @PartialFunction R X)
      (n : nat)
      (x : X)
      (xD : Domain (Xsum fn n) x),
    Domain (fn n) x.
Proof.
  intros. destruct n.
  - assumption.
  - simpl in xD. exact (snd xD).
Defined.

Lemma applyXsum
  : forall {X : Set} {R : ConstructiveReals}
      (fn : nat -> @PartialFunction R X)
      (n : nat)
      (x : X)
      (xD : Domain (Xsum fn n) x)
      (xn : forall n:nat, Domain (fn n) x),
    partialApply (Xsum fn n) x xD
    == CRsum (fun k:nat => partialApply (fn k) x (xn k)) n.
Proof.
  induction n.
  - intros x xD xn. simpl. apply DomainProp.
  - intros x xD xn. simpl.
    rewrite <- (IHn x (fst xD)). clear IHn. destruct xD.
    apply CRplus_morph. reflexivity.
    apply DomainProp.
Qed.

Lemma Xsum_assoc : forall {X : Set} {R : ConstructiveReals}
                     (u : nat -> @PartialFunction R X)
                     (n p : nat)
                     (x : X)
                     (xd : Domain (Xsum u (S n + p)) x)
                     (y : Domain (Xsum u n) x)
                     (z : Domain (Xsum (fun k => u (S n + k)%nat) p) x),
    partialApply (Xsum u (S n + p)) x xd
    == partialApply (Xsum u n) x y
       + partialApply (Xsum (fun k => u (S n + k)%nat) p) x z.
Proof.
  induction p.
  - intros. simpl in z. simpl. destruct xd.
    remember (n + 0)%nat as sn. rewrite plus_0_r in Heqsn. subst sn.
    apply CRplus_morph. apply DomainProp. apply DomainProp.
  - intros. simpl. destruct xd. simpl in z.
    remember (n + S p)%nat as sn. rewrite Nat.add_succ_r in Heqsn. subst sn.
    rewrite (IHp x _ y (fst z)). clear IHp.
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    destruct z. apply CRplus_morph. reflexivity.
    apply DomainProp.
Qed.

Lemma Xsum_assocMinus : forall {X : Set} {R : ConstructiveReals}
                          (u : nat -> @PartialFunction R X)
                          (n p : nat)
                          (x : X)
                          (px : Domain (Xminus (Xsum u (S n + p)) (Xsum u n)) x)
                          (pxD : Domain (Xsum (fun k => u (S n + k)%nat) p) x),
    partialApply (Xminus (Xsum u (S n + p)) (Xsum u n)) x px
    == partialApply (Xsum (fun k => u (S n + k)%nat) p) x pxD.
Proof.
  induction p.
  - intros. simpl in px, pxD.
    transitivity (partialApply (u (S n + 0)%nat) x pxD).
    2: reflexivity. simpl (S n + 0)%nat.
    remember (n + 0)%nat. rewrite Nat.add_0_r in Heqn0. subst n0.
    destruct px. rewrite applyXminus.
    rewrite <- (CRplus_0_r (partialApply (u (S n)) x pxD)). unfold CRminus.
    destruct p. simpl.
    rewrite (CRplus_comm (partialApply (Xsum u n) x d0)).
    rewrite CRplus_assoc. apply CRplus_morph.
    apply DomainProp. rewrite (DomainProp _ _ d0 d).
    rewrite CRplus_opp_r. reflexivity.
  - intros. destruct px.
    rewrite (applyXminus (Xsum u (S n + S p)) (Xsum u n) x d d0).
    simpl. simpl in d. destruct d, pxD. simpl in d3.
    remember (n + S p)%nat. rewrite Nat.add_succ_r in Heqn0. subst n0.
    specialize (IHp x (pair d d0) d2). rewrite <- IHp.
    rewrite (applyXminus (Xsum u (S n + p)) (Xsum u n)).
    unfold CRminus. rewrite (DomainProp _ x d1 d3).
    do 2 rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity.
    rewrite CRplus_comm. reflexivity.
Qed.

Definition XposPart {R : ConstructiveReals} {X : Set}
           (f : @PartialFunction R X) : PartialFunction X
  := Xscale (CR_of_Q _ (1#2)) (Xplus f (Xabs f)).

Lemma applyXposPartNonNeg : forall {X : Set} {R : ConstructiveReals}
                              (f : @PartialFunction R X),
    nonNegFunc (XposPart f).
Proof.
  intros. intros x xdf. unfold XposPart.
  rewrite applyXscale.
  rewrite <- (CRmult_0_r (CR_of_Q _ (1#2))). apply CRmult_le_compat_l_half.
  apply CR_of_Q_pos. reflexivity.
  destruct f,xdf; simpl.
  rewrite <- (CRplus_opp_r (partialApply0 x d)). apply CRplus_le_compat_l.
  setoid_replace (partialApply0 x d0) with (partialApply0 x d).
  rewrite <- CRabs_opp. apply CRle_abs.
  apply DomainProp0.
Qed.

Lemma applyXposPart : forall {X : Set} {R : ConstructiveReals}
                        (f : @PartialFunction R X)
                        (x : X)
                        (xD : Domain f x),
    partialApply (XposPart f) x (pair xD xD)
    == CRmax 0 (partialApply f x xD).
Proof.
  intros. rewrite CRposPartAbsMax. unfold XposPart.
  rewrite applyXscale. rewrite CRmult_comm.
  apply CRmult_morph. 2: reflexivity.
  destruct f; simpl. reflexivity.
Qed.

(* This definition is L-stable, whereas XminConst f 0 is not. *)
Definition XnegPart {X : Set} {R : ConstructiveReals}
           (f : @PartialFunction R X) : PartialFunction X
  := Xscale (CR_of_Q R (1#2)) (Xminus (Xabs f) f).

Lemma applyXnegPartNonNeg : forall {X : Set} {R : ConstructiveReals}
                              (f : @PartialFunction R X),
    nonNegFunc (XnegPart f).
Proof.
  intros. intros y ydf. unfold XnegPart.
  rewrite applyXscale.
  rewrite <- (CRmult_0_r (CR_of_Q _ (1#2))). apply CRmult_le_compat_l_half.
  apply CR_of_Q_pos. reflexivity. destruct ydf; simpl.
  rewrite <- CRopp_mult_distr_l, CRmult_1_l.
  rewrite <- (CRplus_opp_r (partialApply f y d0)).
  apply CRplus_le_compat_r. rewrite (DomainProp f y d0 d).
  apply CRle_abs.
Qed.

Lemma XnegPartAbsMax : forall {R : ConstructiveReals} (x : CRcarrier R),
    CRmax 0 (-x) == (CRabs _ x - x) * (CR_of_Q _ (1#2)).
Proof.
  intros. rewrite CRposPartAbsMax. rewrite CRabs_opp.
  apply CRmult_morph. rewrite CRplus_comm. reflexivity. reflexivity.
Qed.

Lemma applyXnegPart : forall {R : ConstructiveReals} {X : Set}
                        (f : @PartialFunction R X)
                        (x : X)
                        (xD : Domain f x),
    partialApply (XnegPart f) x (pair xD xD)
    == CRmax 0 (- partialApply f x xD).
Proof.
  intros. rewrite XnegPartAbsMax. unfold XnegPart.
  rewrite applyXscale, CRmult_comm. apply CRmult_morph. 2: reflexivity.
  rewrite (applyXminus (Xabs f) f). apply CRplus_morph.
  rewrite applyXabs. apply CRabs_morph. apply DomainProp.
  reflexivity.
Qed.

Lemma applyXnegPartMin : forall {X : Set} {R : ConstructiveReals}
                           (f : @PartialFunction R X)
                           (x : X)
                           (xD : Domain f x),
    partialApply (XnegPart f) x (pair xD xD)
    == - CRmin 0 (partialApply f x xD).
Proof.
  intros. rewrite CRnegPartAbsMin. unfold XnegPart.
  rewrite applyXscale, CRmult_comm.
  rewrite CRopp_mult_distr_l. apply CRmult_morph. 2: reflexivity.
  rewrite (applyXminus (Xabs f) f). unfold CRminus.
  rewrite CRopp_plus_distr, CRopp_involutive, CRplus_comm.
  apply CRplus_morph. reflexivity.
  rewrite applyXabs. apply CRabs_morph. apply DomainProp.
Qed.

Lemma XnegPartNonNeg : forall {R : ConstructiveReals} {X : Set}
                         (f : @PartialFunction R X),
    nonNegFunc (XnegPart f).
Proof.
  intros. intros x xdf. destruct xdf.
  rewrite (DomainProp (XnegPart f) x _ (pair d d)).
  rewrite (applyXnegPart f x d). apply CRmax_l.
Qed.

Lemma SplitPosNegParts : forall {X : Set} {R : ConstructiveReals}
                     (f : @PartialFunction R X)
                     (x : X)
                     (xdf : Domain f x)
                     (xdp : Domain (XposPart f) x)
                     (xdn : Domain (XnegPart f) x),
    partialApply (XposPart f) x xdp - partialApply (XnegPart f) x xdn == partialApply f x xdf.
Proof.
  intros. unfold XposPart, XnegPart, CRminus.
  do 2 rewrite applyXscale.
  destruct xdp. rewrite (applyXplus f (Xabs f)).
  destruct xdn. rewrite (applyXminus (Xabs f) f). rewrite CRplus_comm.
  unfold CRminus. rewrite (DomainProp f x _ xdf), (DomainProp (Xabs f) x _ xdf).
  rewrite CRopp_mult_distr_r, <- CRmult_plus_distr_l.
  rewrite (DomainProp f x d xdf), (DomainProp (Xabs f) x d0 xdf).
  setoid_replace (- (partialApply (Xabs f) x xdf + - partialApply f x xdf) +
                  (partialApply f x xdf + partialApply (Xabs f) x xdf))
    with (partialApply f x xdf + partialApply f x xdf).
  rewrite <- (CRmult_1_l (partialApply f x xdf)), <- CRmult_plus_distr_r.
  rewrite <- CRmult_assoc, CRmult_1_l, <- CR_of_Q_one, <- CR_of_Q_plus.
  rewrite <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * (1+1))%Q with 1%Q.
  rewrite CR_of_Q_one. apply CRmult_1_l.
  reflexivity. rewrite CRplus_comm, CRplus_assoc.
  apply CRplus_morph. reflexivity.
  rewrite CRopp_plus_distr. rewrite CRopp_involutive.
  rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l. reflexivity.
Qed.

Definition Xmin {R : ConstructiveReals} {X : Set}
           (f g : @PartialFunction R X) : PartialFunction X
  := Xminus g (XnegPart (Xminus f g)).

Lemma applyXmin : forall {X : Set} {R : ConstructiveReals}
                    (f g : @PartialFunction R X)
                    (x : X)
                    (xdf : Domain f x)
                    (xdg : Domain g x)
                    (xdp : Domain (Xmin f g) x),
    partialApply (Xmin f g) x xdp
    == CRmin (partialApply f x xdf) (partialApply g x xdg).
Proof.
  intros. unfold Xmin.
  destruct xdp. rewrite (applyXminus g (XnegPart (Xminus f g))).
  assert (Domain (Xminus f g) x).
  { destruct f,g; split. exact xdf. exact xdg. }
  simpl in d0. unfold CRminus.
  rewrite (DomainProp (XnegPart (Xminus f g)) x _ (fst d0, fst d0)),
   applyXnegPartMin.
  destruct d0,p. unfold fst. rewrite (applyXminus f g).
  destruct f, g; simpl.
  rewrite CRopp_involutive. unfold CRminus.
  rewrite (DomainProp1 x d1 d), (DomainProp1 x xdg d), (DomainProp0 x _ xdf).
  rewrite CRmin_plus, CRplus_0_r, (CRplus_comm (partialApply0 x xdf)).
  rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
  apply CRmin_sym.
Qed.

Definition Xmax {R : ConstructiveReals} {X : Set}
           (f g : @PartialFunction R X) : PartialFunction X
  := (Xplus g (XposPart (Xminus f g))).

Lemma applyXmax : forall {X : Set} {R : ConstructiveReals}
                    (f g : @PartialFunction R X)
                    (x : X)
                    (xdf : Domain f x)
                    (xdg : Domain g x)
                    (xdp : Domain (Xmax f g) x),
    partialApply (Xmax f g) x xdp
    == CRmax (partialApply f x xdf) (partialApply g x xdg).
Proof.
  intros. unfold Xmax.
  destruct xdp. rewrite applyXplus.
  assert (Domain (Xminus f g) x).
  { destruct f,g; split. exact xdf. exact xdg. }
  rewrite (DomainProp (XposPart (Xminus f g)) x _ (fst d0, fst d0)),
   applyXposPart.
  destruct d0, d0. unfold fst. rewrite (applyXminus f g).
  destruct f, g; simpl.
  rewrite (DomainProp1 x d2 d), (DomainProp1 x xdg d), (DomainProp0 x d0 xdf).
  unfold CRminus.
  rewrite CRmax_plus, CRplus_0_r, (CRplus_comm (partialApply0 x xdf)).
  rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
  apply CRmax_sym.
Qed.

Lemma XminMultPosDistrib :
  forall {X : Set} {R : ConstructiveReals} (f : PartialFunction X) (a b : CRcarrier R),
    0 <= a
    -> PartialFunExtEq (Xscale a (XminConst f b))
                       (XminConst (Xscale a f) (a*b)).
Proof.
  intros. destruct f; simpl; split; unfold DomainInclusion, Domain.
  - split.
    + intros x xdf. exact xdf.
    + intros x xdf. exact xdf.
  - intros x xdf xg. simpl. rewrite CRmin_mult.
    rewrite (DomainProp0 x xdf xg). reflexivity. exact H.
Qed.

Lemma XscaleAssoc :
  forall {R : ConstructiveReals} {X : Set}
    (f : PartialFunction X) (a b : CRcarrier R),
    PartialFunExtEq (Xscale a (Xscale b f))
                    (Xscale (a*b) f).
Proof.
  intros. destruct f; simpl; split.
  - split.
    + intros x. simpl. exact (fun x => x).
    + intros x. simpl. exact (fun x => x).
  - intros. simpl. rewrite (DomainProp0 x xD xG).
    rewrite CRmult_assoc. reflexivity.
Qed.

Lemma XscaleOne :
  forall {X : Set} {R : ConstructiveReals} (f : @PartialFunction R X),
    PartialFunExtEq (Xscale 1 f) f.
Proof.
  intros. split.
  - split.
    + intros x H. destruct f; exact H.
    + intros x H. destruct f; exact H.
  - intros. rewrite applyXscale, CRmult_1_l.
    apply DomainProp.
Qed.

Lemma XminMultPosDistribOne
  : forall {R : ConstructiveReals} {X : Set}
      (f : PartialFunction X) (a : CRcarrier R) (aPos : 0 < a),
    PartialFunExtEq (Xscale a (XminConst (Xscale (CRinv _ a (inr aPos)) f) 1))
                    (XminConst f a).
Proof.
  intros. split. split.
  - intros x xD. destruct f; exact xD.
  - intros x xD. destruct f; exact xD.
  - intros. rewrite applyXscale.
    simpl in xD, xG.
    rewrite applyXminConst.
    rewrite applyXminConst. rewrite applyXscale.
    rewrite (DomainProp _ _ xD xG). rewrite <- CRmin_mult.
    rewrite <- CRmult_assoc, CRinv_r, CRmult_1_l.
    rewrite CRmult_1_r. reflexivity.
    apply CRlt_asym, aPos.
Qed.

Lemma XmultiTriangleIneg : forall {X : Set} {R : ConstructiveReals}
                             (fn : nat -> @PartialFunction R X)
                             (n : nat)
                             (x : X)
                             (xD : Domain (Xabs (Xsum fn n)) x)
                             (y : Domain (Xsum (fun a : nat => Xabs (fn a)) n) x),
    partialApply (Xabs (Xsum fn n)) x xD
    <= partialApply (Xsum (fun a : nat => Xabs (fn a)) n) x y.
Proof.
  induction n.
  - intros. simpl. simpl in xD.
    rewrite (DomainProp _ _ xD y). apply CRle_refl.
  - intros. simpl. simpl in x,y,xD.
    destruct (Xsum fn n), (fn (S n)), (Xsum (fun a : nat => Xabs (fn a)) n),
    xD, y; simpl; simpl in IHn.
    apply (CRle_trans _ (CRabs _ (partialApply0 x d) + CRabs _ (partialApply1 x d0))).
    apply CRabs_triang.
    apply CRplus_le_compat. apply IHn.
    rewrite (DomainProp1 x d0 d2). apply CRle_refl.
Qed.

(* For partial functions on a product domain, we can project at
   any point in any coordinate, possibly by the empty function. *)
Definition Xproj1 {R : ConstructiveReals} {X Y : Set}
           (f : PartialFunction (prod X Y)) (x : X)
  : PartialFunction Y
  := Build_PartialFunctionXY
       Y (CRcarrier R) (CReq R) (fun y:Y => Domain f (x,y))
       (fun y yD => partialApply f (x,y) yD)
       (fun y p q => DomainProp f (x,y) p q).

Definition Xproj2 {R : ConstructiveReals} {X Y : Set}
           (f : PartialFunction (prod X Y)) (y : Y)
  : PartialFunction X
  := Build_PartialFunctionXY
       X (CRcarrier R) (CReq R) (fun x:X => Domain f (x,y))
       (fun x xD => partialApply f (x,y) xD)
       (fun x p q => DomainProp f (x,y) p q).
