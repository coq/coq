(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(* We complete an integration space IS by countable limits of L-functions.
   Those limit functions are called integrable functions and the integral I
   extends to them. Hence we obtain a bigger integration space IScomplete,
   which L-functions are the integrable functions of IS.

   IScomplete is complete, in the sense that its integrable functions are
   already integrable functions of IS : no new functions are added. *)

Require Import QArith.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructivePartialFunctions.
Require Import CMTbase.

Local Open Scope ConstructiveReals.


(* A function f is integrable iif it is the pointwise limit
   almost everywhere of a sequence of L-functions, which integrals converge.
   Keep the convergence proof in sort Prop at the moment, so that
   it is unique. *)

(* A series of elementary integrals, that converges absolutely. *)
Record IntegralRepresentation {IS : IntegrationSpace} : Type
  := {
      IntFn : nat -> PartialFunction (X (ElemFunc IS));
      IntFnL : forall n:nat, L (ElemFunc IS) (IntFn n);
      IntAbsSum : CRcarrier (RealT (ElemFunc IS));
      (* Convergence with computable modulus, we want to extract it. *)
      IntAbsSumCv : series_cv (fun k:nat => Iabs (IntFn k) (IntFnL k)) IntAbsSum
    }.

(* A function f is integrable when it is the limit almost everywhere of
   the L-series fn. Here "almost everywhere" is encoded as where
   the series fn converges absolutely. It is equivalent to Daniell's
   definition of null sets. *)

Lemma IntAbsSumPos : forall {IS : IntegrationSpace}
                       (fInt : @IntegralRepresentation IS),
    0 <= IntAbsSum fInt.
Proof.
  intros. destruct fInt; simpl.
  apply (series_cv_nonneg ((fun k : nat => Iabs (IntFn0 k) (IntFnL0 k)))).
  intros. apply integralPositive. intros. intros x xdf.
  rewrite applyXabs.
  apply CRabs_pos. assumption.
Qed.

Lemma represApply : forall {IS : IntegrationSpace}
                      (f : PartialFunction (X (ElemFunc IS)))
                      (fInt : IntegralRepresentation)
                      (isFInt : PartialRestriction (XinfiniteSumAbs (IntFn fInt)) f)
                      (x : X (ElemFunc IS))
                      (xS : Domain (XinfiniteSumAbs (IntFn fInt)) x)
                      (y : Domain f x),
    series_cv
      (fun n : nat => partialApply (IntFn fInt n) x
                              (domainInfiniteSumAbsIncReverse
                                 (IntFn fInt) x xS n))
      (partialApply f x y).
Proof.
  intros. destruct isFInt as [i appX].
  specialize (appX x xS y).
  apply (CR_cv_proper _ (partialApply (XinfiniteSumAbs (IntFn fInt)) x xS)).
  2: exact appX. clear appX.
  simpl. destruct xS; simpl.
  destruct (series_cv_abs (fun n : nat => partialApply (IntFn fInt n) x (x0 n))).
  exact s.
Qed.

Definition IntegrableFunction {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS))) : Type
  := { fInt : IntegralRepresentation
              & PartialRestriction (XinfiniteSumAbs (IntFn fInt)) f }.

(* As proven by INonDecreasing, L-functions on X are defined
   almost everywhere on X. So the previous definition can be
   summarized : the infinite sum of fn converges almost everywhere to f
   and the integral of f is the infinite sum of the integrals of fn. *)

Definition IntegrableFunctionExtensional
           {IS : IntegrationSpace}
           (f g : PartialFunction (X (ElemFunc IS)))
  : PartialRestriction f g
    -> IntegrableFunction f
    -> IntegrableFunction g.
Proof.
  intros [inj restr] [rep [injF isrep]]. exists rep.
  split.
  - exact (fun x xS => inj x (injF x xS)).
  - intros. rewrite (isrep x _ (injF x xD)).
    apply restr.
Defined.

(* This will be redefined shortly after as the integral of
   XinfiniteSumAbs (IntFn fInt).
   This definition is rarely used directly. *)
Definition IntegralSeries {IS : IntegrationSpace}
           (fInt : @IntegralRepresentation IS) : CRcarrier (RealT (ElemFunc IS)).
Proof.
  destruct fInt; simpl.
  destruct (series_cv_maj (fun n : nat => I IS (IntFn0 n) (IntFnL0 n))
                          (fun k : nat => Iabs (IntFn0 k) (IntFnL0 k)) IntAbsSum0).
  intro n. apply integralAbsMaj.
  assumption. exact x.
Defined.

Definition Integral {IS : IntegrationSpace}
           {f : PartialFunction (X (ElemFunc IS))}
           (fInt : IntegrableFunction f)
  := IntegralSeries (let (i,_) := fInt in i).

Definition IntegralCv {IS : IntegrationSpace}
           (fInt : IntegralRepresentation)
  : series_cv (fun n : nat => (I IS (IntFn fInt n)
                            (IntFnL fInt n)))
              (IntegralSeries fInt).
Proof.
  destruct fInt; simpl.
  destruct (series_cv_maj (fun n : nat => I IS (IntFn0 n) (IntFnL0 n))
                          (fun k : nat => Iabs (IntFn0 k) (IntFnL0 k)) IntAbsSum0).
  apply p.
Qed.

(*
  An extension of an integrable function has the same integral.
  In particular, if the domain of an L-function g is included
  in the domain of a function f, and if f equals zero on the
  domain of g, then f is integrable with integral 0.
  Multiply g by 0 and apply this lemma to demonstrate it.
  In other words, L-functions are defined almost everywhere.
 *)
Lemma IntegralRestrict : forall {IS : IntegrationSpace}
                           (f g : PartialFunction (X (ElemFunc IS)))
                           (fInt : IntegrableFunction f)
                           (restrict : PartialRestriction f g),
    Integral (IntegrableFunctionExtensional f g restrict fInt)
    = Integral fInt.
Proof.
  intros.
  destruct fInt, restrict, p; simpl.
  reflexivity.
Qed.

(* We now prove that the integral of f does not depend on the representation fn.
   If gn is another representation of f, we will prove that the sequence
   f0, -g0, f1, -g1, f2, -g2, ...
   is a representation of the zero function, with integral 0. Note that the
   sequence f0-g0, f1-g1, ... does not work, because the convergence of
   Sum_n |fn - gn| does not imply the convergence of Sum_n |fn|.

   So we first need to combine two sequences into one. Of course, we can
   iterate this to combine any finite number of sequences into one. *)

Definition weaveSequences (X : Type) (fn gn : nat -> X)
  : nat -> X
  := fun n => if Nat.even n then fn (n / 2)%nat else gn (n / 2)%nat.

Definition weaveSequencesL
           (E : FunctionRieszSpace)
           (fn : nat -> PartialFunction (X E))
           (fnL : forall n:nat, L E (fn n))
           (gn : nat -> PartialFunction (X E))
           (gnL : forall n:nat, L E (gn n))
  : forall n:nat, L E (weaveSequences (PartialFunction (X E))
                                           fn gn n).
Proof.
  intros. unfold weaveSequences. destruct (Nat.even n). apply fnL. apply gnL.
Defined.

Lemma evenSuccessor : forall n:nat, Nat.even (S n) = negb (Nat.even n).
Proof.
  induction n. reflexivity. rewrite IHn. simpl.
  destruct (Nat.even n); reflexivity.
Qed.

Lemma weaveSequencesEven : forall (X : Set) (fn gn : nat -> X) (n : nat),
    weaveSequences X fn gn (n*2) = fn n.
Proof.
  intros. unfold weaveSequences. destruct (Nat.even (n * 2)) eqn:even.
  rewrite Nat.div_mul. reflexivity. discriminate.
  exfalso. assert (Nat.even (n * 2) = true).
  apply Nat.even_spec. exists n. rewrite mult_comm. reflexivity.
  rewrite even in H. discriminate.
Qed.

Lemma weaveSequencesOdd : forall (X : Set) (fn gn : nat -> X) (n : nat),
    weaveSequences X fn gn (1 + n*2) = gn n.
Proof.
  intros. unfold weaveSequences. destruct (Nat.even (1 + n * 2)) eqn:even.
  exfalso. rewrite evenSuccessor in even. assert (Nat.even (n * 2) = true).
  apply Nat.even_spec. exists n. rewrite mult_comm. reflexivity.
  rewrite H in even. discriminate. rewrite Nat.div_add. simpl.
  reflexivity. auto.
Qed.

Lemma divModSucc : forall n p q : nat,
    fst (Nat.divmod n 1 (S q) p) = S (fst (Nat.divmod n 1 q p)).
Proof.
  induction n.
  - intros. reflexivity.
  - intros. simpl. destruct p. rewrite IHn. reflexivity.
    rewrite IHn. reflexivity.
Qed.

Lemma weaveSequencesSum : forall {R : ConstructiveReals}
                            (fn gn : nat -> CRcarrier R) (n : nat),
    CRsum (fun k:nat => (weaveSequences (CRcarrier R) fn gn k)) n
    == CRsum fn (n / 2)
       + match n with
         | O => 0
         | _ => CRsum gn (if Nat.even n then pred (n / 2) else n / 2)
         end.
Proof.
  induction n.
  - unfold weaveSequences. simpl. rewrite CRplus_0_r. reflexivity.
  - simpl. rewrite IHn. clear IHn. destruct n. unfold weaveSequences. simpl.
    rewrite CRplus_0_r. reflexivity.
    assert (fst (Nat.divmod n 1 0 1) = n/2 )%nat. { reflexivity. }
    assert (fst (Nat.divmod n 1 0 0) = (1+n)/2 )%nat. { reflexivity. }

    unfold weaveSequences. simpl. destruct (Nat.even n) eqn:nEven.
    + destruct n. simpl.
      rewrite CRplus_assoc, (CRplus_comm (gn 0%nat)).
      rewrite <- CRplus_assoc. reflexivity.
      destruct (Nat.even n) eqn:snEven.
      rewrite evenSuccessor in nEven. rewrite snEven in nEven. inversion nEven.
      rewrite divModSucc. rewrite H. rewrite H0.
      pose proof (Nat.even_spec (S n)) as [H1 _].
      destruct (H1 nEven). rewrite mult_comm in H2.
      rewrite H2. rewrite Nat.div_add. rewrite Nat.div_mul.
      simpl. do 2 rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
      apply CRplus_comm. auto. auto.
    + destruct n. exfalso. inversion nEven. destruct (Nat.even n) eqn:snEven.
      rewrite divModSucc. rewrite H. rewrite H0.
      pose proof (Nat.odd_spec (S n)) as [H1 _]. destruct H1. unfold Nat.odd.
      rewrite nEven. trivial. rewrite mult_comm in H1. rewrite plus_comm in H1.
      rewrite H1. rewrite Nat.div_add.
      assert ((1 + (1 + x * 2)) / 2 = (2 + x * 2) / 2)%nat. reflexivity.
      rewrite H2. rewrite Nat.div_add. simpl.
      do 2 rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
      apply CRplus_morph. reflexivity. reflexivity.
      auto. auto.
      exfalso. rewrite <- nEven in snEven.
      rewrite evenSuccessor in snEven. destruct (Nat.even n); discriminate.
Qed.

Lemma partialApplyWeave
  : forall {R : ConstructiveReals} (X : Set)
      (fn gn : nat -> @PartialFunction R X)
      (n : nat)
      (x : X)
      (xH : Domain (fn (n/2)%nat) x)
      (y : Domain (gn (n/2)%nat) x)
      (z : Domain (weaveSequences (PartialFunction X) fn gn n) x),
    partialApply (weaveSequences (PartialFunction X) fn gn n) x z
    == if Nat.even n then partialApply (fn (n/2)%nat) x xH
       else partialApply (gn (n/2)%nat) x y.
Proof.
  intros. unfold weaveSequences. unfold weaveSequences in z.
  unfold weaveSequences in xH.
  destruct (Nat.even n); apply DomainProp.
Qed.

Definition domainWeaveEvenInc {R : ConstructiveReals} (X : Set)
           (fn gn : nat -> @PartialFunction R X)
           (n : nat)
           (x : X)
           (xD : Domain (weaveSequences _ fn gn (n*2)) x)
  : Domain (fn n) x.
Proof.
  unfold weaveSequences. unfold weaveSequences in xD.
  destruct (Nat.even (n*2)) eqn:des.
  - remember (n*2/2)%nat. rewrite Nat.div_mul in Heqn0. subst n0.
    exact xD. auto.
  - exfalso. assert (Nat.even (n * 2) = true).
    apply Nat.even_spec. exists n. rewrite mult_comm. reflexivity.
    rewrite des in H. discriminate.
Qed.

Lemma partialApplyWeaveEven
  : forall {R : ConstructiveReals} (X : Set)
      (fn gn : nat -> @PartialFunction R X)
      (n : nat)
      (x : X)
      (xD : Domain (fn n) x)
      (y : Domain (weaveSequences (PartialFunction X) fn gn (n*2)) x),
    partialApply (fn n) x xD
    == partialApply (weaveSequences (PartialFunction X) fn gn (n * 2)) x y.
Proof.
  intros. unfold weaveSequences. unfold weaveSequences in y.
  destruct (Nat.even (n * 2)) eqn:des.
  (* Hide 2 * n / 2 in a single variable, to substitute it *)
  remember ((n * 2) / 2)%nat as doubleN. rewrite Nat.div_mul in HeqdoubleN.
  subst doubleN. apply DomainProp. auto.
  exfalso. assert (Nat.even (n * 2) = true).
  apply Nat.even_spec. exists n. rewrite mult_comm. reflexivity. rewrite des in H.
  discriminate.
Qed.

Definition domainWeaveOddInc {R : ConstructiveReals} (X : Set)
           (fn gn : nat -> @PartialFunction R X)
           (n : nat)
           (x : X)
           (xD : Domain (weaveSequences _ fn gn (1+n*2)) x)
  : Domain (gn n) x.
Proof.
  unfold weaveSequences. unfold weaveSequences in xD.
  destruct (Nat.even (1+n*2)) eqn:des.
  - exfalso. assert (Nat.odd (1+ n * 2) = true).
    apply Nat.odd_spec. exists n. rewrite mult_comm.
    rewrite plus_comm. reflexivity.
    unfold Nat.odd in H. rewrite des in H. discriminate.
  - remember ((1+n*2)/2)%nat. rewrite Nat.div_add in Heqn0. subst n0.
    exact xD. auto.
Qed.

Lemma partialApplyWeaveOdd
  : forall {R : ConstructiveReals} (X : Set)
      (fn gn : nat -> @PartialFunction R X)
      (n : nat)
      (x : X)
      (xD : Domain (gn n) x)
      (y : Domain (weaveSequences (PartialFunction X) fn gn (1 + (n*2))) x),
    partialApply (gn n) x xD
    == partialApply (weaveSequences (PartialFunction X) fn gn (1 + (n * 2))) x y.
Proof.
  intros. unfold weaveSequences. unfold weaveSequences in y.
  destruct (Nat.even (1+(n * 2))) eqn:even.
  exfalso. assert (Nat.even (n * 2) = true).
  apply Nat.even_spec. exists n. rewrite mult_comm. reflexivity.
  rewrite evenSuccessor in even.
  rewrite H in even. discriminate.
  (* Hide 2 * n / 2 in a single variable, to substitute it *)
  remember ((1 + (n * 2)) / 2)%nat as doubleN.
  rewrite Nat.div_add in HeqdoubleN. simpl in HeqdoubleN. subst doubleN.
  apply DomainProp. auto.
Qed.

Lemma halfWeavedSumEven : forall {R : ConstructiveReals}
                            (fn gn : nat -> CRcarrier R) (a : CRcarrier R),
    (forall k:nat, 0 <= fn k)
    -> (forall k:nat, 0 <= gn k)
    -> series_cv (weaveSequences (CRcarrier R) fn gn) a
    -> { l : CRcarrier R & series_cv fn l }.
Proof.
  intros.
  destruct (series_cv_maj (weaveSequences (CRcarrier R) fn (fun n => 0))
                          (weaveSequences (CRcarrier R) fn gn) a) as [l [cv _]].
  - intro n. unfold weaveSequences. destruct (Nat.even n).
    rewrite CRabs_right. apply CRle_refl. apply H.
    rewrite CRabs_right. apply H0. apply CRle_refl.
  - assumption.
  - exists l. intros n.
    specialize (cv n) as [N cv].
    exists N. intros. specialize (cv (i*2)%nat).
    rewrite weaveSequencesSum in cv. rewrite Nat.div_mul in cv.
    setoid_replace (match (i * 2)%nat with
           | 0%nat => CRzero R
           | S _ =>
               CRsum (fun _ : nat => 0)
                 (if Nat.even (i * 2) then Init.Nat.pred i else i)
           end) with (CRzero R) in cv.
    rewrite CRplus_0_r in cv. apply cv. apply (le_trans _ i).
    assumption. rewrite mult_comm. simpl. rewrite <- (plus_0_r i).
    rewrite <- plus_assoc. apply Nat.add_le_mono_l. apply le_0_n.
    destruct (i*2)%nat eqn:des. reflexivity.
    rewrite sum_const. rewrite CRmult_0_l. reflexivity. auto.
Qed.

Lemma halfWeavedSumOdd : forall {R : ConstructiveReals}
                           (fn gn : nat -> CRcarrier R) (a : CRcarrier R),
    (forall k:nat, 0 <= fn k)
    -> (forall k:nat, 0 <= gn k)
    -> series_cv (weaveSequences (CRcarrier R) fn gn) a
    -> { l : CRcarrier R & series_cv gn l }.
Proof.
  intros.
  destruct (series_cv_maj (weaveSequences (CRcarrier R) (fun n => 0) gn)
                          (weaveSequences (CRcarrier R) fn gn) a) as [l [cv _]].
  - intro n. unfold weaveSequences. destruct (Nat.even n).
    rewrite CRabs_right. apply H. apply CRle_refl.
    rewrite CRabs_right. apply CRle_refl. apply H0.
  - assumption.
  - exists l. intros p. specialize (cv p) as [N cv].
    exists N. intros n H2. specialize (cv (1+n*2)%nat).
    rewrite weaveSequencesSum in cv. rewrite Nat.div_add in cv.
    rewrite sum_const in cv. rewrite CRmult_0_l in cv. rewrite CRplus_0_l in cv.
    destruct (1 + n*2)%nat eqn:des.
    + exfalso. inversion des.
    + rewrite <- des in cv. clear des. destruct (Nat.even (1+n*2)) eqn:des.
      exfalso. assert (Nat.Odd (1+n*2)). exists n. rewrite plus_comm.
      rewrite mult_comm. reflexivity. apply Nat.odd_spec in H3.
      unfold Nat.odd in H3. rewrite des in H3. inversion H3.
      apply cv. apply (le_trans N n). assumption.
      apply (le_trans n (n*2)). rewrite <- (mult_1_r n).
      rewrite <- mult_assoc. apply Nat.mul_le_mono_nonneg_l.
      apply le_0_n. apply le_S. apply le_refl.
      rewrite <- (plus_0_l (n*2)). rewrite plus_assoc.
      apply Nat.add_le_mono_r. auto.
    + auto.
Qed.

Lemma weaveInfiniteSums
  : forall {R : ConstructiveReals} (u v : nat -> CRcarrier R) (su sv : CRcarrier R),
    series_cv u su
    -> series_cv v sv
    -> series_cv (weaveSequences (CRcarrier R) u v) (su + sv).
Proof.
  intros. intros n.
  specialize (H (2*n)%positive). specialize (H0 (2*n)%positive).
  destruct H as [N H], H0 as [N0 H0].
  exists (S(N*2 + (S N0)*2)). intros.
  rewrite weaveSequencesSum. destruct i. exfalso; inversion H1.
  destruct (Nat.even (S i)) eqn:snEven.
  + setoid_replace (CRsum u (S i / 2)
                    + CRsum v (Init.Nat.pred (S i / 2)) - (su + sv))
      with (CRsum u (S i / 2) - su + (CRsum v (Init.Nat.pred (S i / 2)) - sv)).
    apply (CRle_trans _ _ _ (CRabs_triang _ _)).
    setoid_replace (1 # n)%Q with ((1 # (2*n)) + (1 # (2*n)))%Q.
    apply le_S_n in H1. rewrite CR_of_Q_plus. apply CRplus_le_compat.
    apply H. rewrite <- (Nat.div_mul N 2). apply Nat.div_le_mono.
    auto. apply (le_trans (N*2) (N*2 + (S N0)*2)). apply Nat.le_add_r.
    apply (le_trans _ i). assumption.
    apply le_S. apply le_refl. auto.
    apply H0. assert (N0 = pred (S N0)). reflexivity.
    rewrite H2. apply le_pred. rewrite <- (Nat.div_mul (S N0) 2).
    apply Nat.div_le_mono. auto.
    apply (le_trans _ (N*2 + (S N0)*2)).
    rewrite plus_comm. apply Nat.le_add_r.
    apply (le_trans (N*2 + (S N0)*2) i). assumption. apply le_S. apply le_refl. auto.
    rewrite Qinv_plus_distr. reflexivity.
    unfold CRminus. do 2 rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity. rewrite CRopp_plus_distr, CRplus_comm.
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity. apply CRplus_comm.
  + setoid_replace (CRsum u (S i / 2) + CRsum v (S i / 2) - (su + sv))
      with (CRsum u (S i / 2) - su + (CRsum v (S i / 2) - sv)).
    apply (CRle_trans _ _ _ (CRabs_triang _ _)).
    setoid_replace (1 # n)%Q with ((1 # (2*n)) + (1 # (2*n)))%Q.
    apply le_S_n in H1. rewrite CR_of_Q_plus. apply CRplus_le_compat.
    apply H. rewrite <- (Nat.div_mul N 2). apply Nat.div_le_mono.
    auto. apply (le_trans (N*2) (N*2 + (S N0)*2)). apply Nat.le_add_r.
    apply (le_trans _ i). assumption. apply le_S. apply le_refl. auto.
    apply H0. rewrite <- (Nat.div_mul N0 2).
    apply Nat.div_le_mono. auto.
    apply (le_trans (N0*2) (N*2 + (S N0)*2)). rewrite plus_comm.
    apply (le_trans (N0 * 2) (S N0 * 2)).
    apply mult_le_compat_r. apply le_S. apply le_refl.
    apply Nat.le_add_r.
    apply (le_trans _ i). assumption. apply le_S. apply le_refl. auto.
    rewrite Qinv_plus_distr. reflexivity.
    unfold CRminus. do 2 rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity. rewrite CRopp_plus_distr, CRplus_comm.
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity. apply CRplus_comm.
Qed.

Lemma sum_truncate_above : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (N n : nat),
    le N n -> CRsum (fun n0 : nat => if le_dec n0 N then u n0 else 0) n
              == CRsum u N.
Proof.
  intros. destruct (Nat.eq_dec N n).
  - subst N. apply CRsum_eq. intros. destruct (le_dec i n).
    reflexivity. contradiction.
  - (* N < n so we can split the sum in 2 and use sum_assoc. *)
    destruct (Nat.le_exists_sub (S N) n) as [p [H0 _]].
    + pose proof (Nat.lt_ge_cases N n) as [H0|H1]. apply H0. exfalso.
      exact (n0 (le_antisym N n H H1)).
    + subst n. rewrite plus_comm. rewrite sum_assoc.
      assert (CRsum (fun k : nat => if le_dec (S N + k) N then u (S N + k)%nat else 0) p == 0).
      { rewrite <- (CRsum_eq (fun k => 0)). rewrite sum_const.
        apply CRmult_0_l. intros.
        destruct (le_dec (S N + i)). exfalso. assert (S N <= N)%nat.
        apply (le_trans (S N) (S N + i)). apply Nat.le_add_r. assumption.
        exact (Nat.nle_succ_diag_l N H1). reflexivity. }
      rewrite H0. rewrite CRplus_0_r.
      rewrite (CRsum_eq u (fun n1 : nat => if le_dec n1 N then u n1 else 0)).
      reflexivity. intros. destruct (le_dec i N). reflexivity. contradiction.
Qed.

Lemma infinite_sum_truncate_below
  : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (s : CRcarrier R) (N : nat),
    series_cv u s
    -> series_cv (fun n : nat => if le_dec n N then 0 else u n)
                    (s - CRsum u N).
Proof.
  intros.
  apply (series_cv_eq
           (fun n : nat => u n + (if le_dec n N then (-u n) else 0))).
  intros. destruct (le_dec n N). rewrite CRplus_opp_r. reflexivity.
  rewrite CRplus_0_r. reflexivity.
  apply series_cv_plus. assumption. intros n. exists N. intros.
  rewrite sum_truncate_above.
  rewrite <- (CRsum_eq (fun n0 : nat => u n0 * (CRopp R 1))).
  rewrite sum_scale, CRmult_comm.
  rewrite <- (CRopp_mult_distr_l 1). unfold CRminus.
  rewrite <- CRopp_plus_distr.
  rewrite CRabs_opp. rewrite CRmult_1_l.
  rewrite CRplus_opp_r. rewrite CRabs_right.
  rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRle_refl.
  intros. rewrite <- CRopp_mult_distr_r, CRmult_1_r.
  reflexivity. assumption.
Qed.

Lemma partialApplyWeaveInfiniteSum
  : forall {R : ConstructiveReals} (X : Set)
      (fn gn : nat -> @PartialFunction R X)
      (x : X)
      (xD : Domain (XinfiniteSumAbs fn) x)
      (y : Domain (XinfiniteSumAbs gn) x)
      (pxDn : forall n:nat, Domain (weaveSequences (PartialFunction X) fn gn n) x),
    series_cv
      (fun n : nat =>
         partialApply (weaveSequences (PartialFunction X) fn gn n) x
                      (pxDn n))
      (partialApply (XinfiniteSumAbs fn) x xD
       + partialApply (XinfiniteSumAbs gn) x y).
Proof.
  intros.
  apply (series_cv_eq
           (weaveSequences
              (CRcarrier R) (fun n => partialApply
                         (fn n) x (domainInfiniteSumAbsIncReverse _ x xD n))
              (fun n => partialApply
                       (gn n) x (domainInfiniteSumAbsIncReverse _ x y n)))).
  intro n. destruct (Nat.even n) eqn:nEven.
  - pose proof (Nat.even_spec n) as [H2 _]. destruct (H2 nEven) as [m H3]. subst n.
    rewrite mult_comm.
    rewrite <- (partialApplyWeaveEven
                 X fn gn m x (domainInfiniteSumAbsIncReverse _ x xD m)).
    + rewrite weaveSequencesEven. reflexivity.
  - pose proof (Nat.odd_spec n) as [H2 _]. destruct H2 as [m H3]. unfold Nat.odd.
    rewrite nEven. trivial. subst n. rewrite plus_comm. rewrite mult_comm.
    rewrite <- (partialApplyWeaveOdd
                 X fn gn m x (domainInfiniteSumAbsIncReverse _ x y m)).
    + rewrite weaveSequencesOdd. reflexivity.
  - apply weaveInfiniteSums.
    apply applyInfiniteSumAbs. reflexivity.
    apply applyInfiniteSumAbs. reflexivity.
Qed.

(* The Prop part, hidden behind a Qed.
   The exposed part in sort Type comes right after. *)
Definition IntegralRepresentationZero {IS : IntegrationSpace}
  : @IntegralRepresentation IS.
Proof.
  apply (Build_IntegralRepresentation IS
           (fun _ : nat => Izero IS)
           (fun _ : nat => Izero_is_L IS)
           0).
  apply (series_cv_eq (fun n => 0)). intro n.
  unfold Iabs. rewrite <- (Izero_is_zero IS).
  apply IExtensional. intros. unfold Izero.
  rewrite applyXscale. rewrite CRmult_0_l.
  rewrite applyXabs. rewrite applyXscale. rewrite CRmult_0_l.
  rewrite CRabs_right. reflexivity. apply CRle_refl.
  intros n. exists O. intros.
  rewrite sum_const. rewrite CRmult_0_l. unfold CRminus.
  rewrite CRplus_0_l, CRopp_0.
  rewrite CRabs_right. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  apply CRle_refl.
Defined.

Lemma IntegrableZeroMaj : forall {IS : IntegrationSpace},
    PartialRestriction (XinfiniteSumAbs (IntFn (IntegralRepresentationZero)))
                       (Xconst (X (ElemFunc IS)) 0).
Proof.
  split.
  - intros x [xn cv]. simpl. trivial.
  - intros. destruct xD as [xn cv]. transitivity (CRzero (RealT (ElemFunc IS))).
    apply applyInfiniteSumAbs.
    apply (series_cv_eq (fun _ => 0)).
    intro n. unfold IntegralRepresentationZero, IntFn.
    rewrite applyIzero. reflexivity.
    intros p. exists O. intros. rewrite sum_const.
    rewrite CRmult_0_l. unfold CRminus.
    rewrite CRplus_opp_r, CRabs_right.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le.
    discriminate. apply CRle_refl. reflexivity.
Qed.

Definition IntegrableZero {IS : IntegrationSpace}
  : IntegrableFunction (Xconst (X (ElemFunc IS)) 0).
Proof.
  exists (IntegralRepresentationZero). apply IntegrableZeroMaj.
Defined.

Lemma IntegralZeroIsZero : forall {IS : IntegrationSpace},
    Integral (@IntegrableZero IS) == 0.
Proof.
  intros IS; unfold Integral.
  pose proof (IntegralCv (@IntegralRepresentationZero IS)).
  apply (series_cv_unique (fun _ : nat => I IS (Izero IS) (Izero_is_L IS))).
  assumption.
  apply (CR_cv_eq _ (fun _ => 0)). 2: apply CR_cv_const.
  intros. rewrite sum_const. unfold Izero. unfold Izero_is_L.
  rewrite Ihomogeneous. rewrite CRmult_0_l.
  rewrite CRmult_0_l. reflexivity.
Qed.

Definition domainInfinSumWeaveL {R : ConstructiveReals} (X : Set)
           (fn gn : nat -> @PartialFunction R X)
           (x : X)
           (xD : Domain (XinfiniteSumAbs (weaveSequences _ fn gn)) x)
  : Domain (@XinfiniteSumAbs R _ fn) x.
Proof.
  pose (fun n => domainWeaveEvenInc
                X fn gn n x (domainInfiniteSumAbsIncReverse _ x xD (n*2)))
    as pxDFn.
  pose (fun n => domainWeaveOddInc
                X fn gn n x (domainInfiniteSumAbsIncReverse _ x xD (1+n*2)))
    as pxDGn.
  destruct xD as [xn cv]; simpl in pxDFn, pxDGn.
  pose proof (CR_complete R _ cv) as [lim cv2].
  destruct (halfWeavedSumEven
              (fun n => CRabs _ (partialApply (fn n) x (pxDFn n)))
              (fun n => CRabs _ (partialApply (gn n) x (pxDGn n)))
              lim) as [l cvl].
  intro k. apply CRabs_pos. intro k. apply CRabs_pos.
  apply (CR_cv_eq _ (CRsum
             (fun k : nat =>
              CRabs _
                (partialApply (weaveSequences (PartialFunction X) fn gn k) x (xn k))))).
  2: apply cv2.
  intro n. apply CRsum_eq. intros.
  rewrite (partialApplyWeave X fn gn i x (pxDFn (i/2)%nat) (pxDGn (i/2)%nat)).
  - unfold weaveSequences. destruct (Nat.even i); reflexivity.
  - exists pxDFn. exact (Rcv_cauchy_mod _ l cvl).
Qed.

Definition domainInfinSumWeaveR {R : ConstructiveReals} (X : Set)
           (fn gn : nat -> PartialFunction X)
           (x : X)
           (xD : Domain (XinfiniteSumAbs (weaveSequences _ fn gn)) x)
  : Domain (@XinfiniteSumAbs R _ gn) x.
Proof.
  pose (fun n => domainWeaveEvenInc
                X fn gn n x (domainInfiniteSumAbsIncReverse _ x xD (n*2)))
    as pxDFn.
  pose (fun n => domainWeaveOddInc
                X fn gn n x (domainInfiniteSumAbsIncReverse _ x xD (1+n*2)))
    as pxDGn.
  destruct xD as [xn cv]; simpl in pxDFn, pxDGn.
  pose proof (CR_complete R _ cv) as [lim cv2].
  destruct (halfWeavedSumOdd
              (fun n => CRabs _ (partialApply (fn n) x (pxDFn n)))
              (fun n => CRabs _ (partialApply (gn n) x (pxDGn n)))
              lim) as [l cvl].
  intro k. apply CRabs_pos. intro k. apply CRabs_pos.
  apply (CR_cv_eq _ (CRsum
             (fun k : nat =>
              CRabs _
                (partialApply (weaveSequences (PartialFunction X) fn gn k) x (xn k))))).
  2: apply cv2.
  intro n. apply CRsum_eq. intros.
  rewrite (partialApplyWeave X fn gn i x (pxDFn (i/2)%nat) (pxDGn (i/2)%nat)).
  - unfold weaveSequences. destruct (Nat.even i); reflexivity.
  - exists pxDGn. exact (Rcv_cauchy_mod _ l cvl).
Qed.

Definition IntegralRepresentationPlus
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fInt : IntegrableFunction f)
           (g : PartialFunction (X (ElemFunc IS)))
           (gInt : IntegrableFunction g)
  : @IntegralRepresentation IS.
Proof.
  destruct fInt as [fInt injF], gInt as [gInt injG].
  apply (Build_IntegralRepresentation
           IS _
           (weaveSequencesL (ElemFunc IS) (IntFn fInt) (IntFnL fInt)
                            (IntFn gInt) (IntFnL gInt))
           (IntAbsSum fInt + IntAbsSum gInt)).
  (* Limit of sum of integrals of absolute values *)
  destruct fInt, gInt; simpl.
  apply (series_cv_eq (weaveSequences (CRcarrier (RealT (ElemFunc IS)))
                                      (fun n => Iabs (IntFn0 n) (IntFnL0 n))
                                      (fun n => Iabs (IntFn1 n) (IntFnL1 n)))).
  intro n. unfold weaveSequences. unfold weaveSequencesL.
  destruct (Nat.even n); reflexivity.
  apply weaveInfiniteSums; assumption.
Defined.

Definition IntegralRepresentationPlusInj
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fInt : IntegrableFunction f)
           (g : PartialFunction (X (ElemFunc IS)))
           (gInt : IntegrableFunction g)
           (x : X (ElemFunc IS))
           (xD : Domain (XinfiniteSumAbs
                           (IntFn (IntegralRepresentationPlus f fInt g gInt))) x)
  : Domain (Xplus f g) x.
Proof.
  destruct fInt as [[fn fnL] [fInj resF]].
  destruct gInt as [[gn gnL] [gInj resG]].
  unfold IntegralRepresentationPlus, IntFn in x.
  pose proof (domainInfinSumWeaveL _ fn gn x) as ixf.
  pose proof (domainInfinSumWeaveR _ fn gn x) as ixg.
  simpl in resF.
  pose proof (resF x (ixf xD)) as yf.
  exact (pair (fInj x (ixf xD)) (gInj x (ixg xD))).
Qed.

Lemma IntegrablePlusMaj
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (g : PartialFunction (X (ElemFunc IS)))
      (gInt : IntegrableFunction g),
    PartialRestriction (XinfiniteSumAbs
                          (IntFn (IntegralRepresentationPlus f fInt g gInt)))
                       (Xplus f g).
Proof.
  (* The weaved absolute convergence implies both that of fn and of gn. *)
  split.
  - intros x xd.
    exact (IntegralRepresentationPlusInj f fInt g gInt x xd).
  - intros. apply applyInfiniteSumAbs.
    destruct fInt as [[fn fnL] [fInj resF]];
    destruct gInt as [[gn gnL] [gInj resG]];
    unfold IntegralRepresentationPlus, IntFn.
    unfold IntegralRepresentationPlus, IntFn in xD.
    pose proof (domainInfinSumWeaveL _ fn gn x xD) as ixf.
    pose proof (domainInfinSumWeaveR _ fn gn x xD) as ixg.
    specialize (resF x ixf) as appF.
    specialize (resG x ixg) as appG. simpl in appG, appF.
    destruct xG. rewrite (applyXplus f g).
    rewrite <- appG. rewrite <- appF.
    apply partialApplyWeaveInfiniteSum.
Qed.

Definition IntegrablePlus {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (g : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction g
    -> IntegrableFunction (Xplus f g).
Proof.
  intros fInt gInt.
  exists (IntegralRepresentationPlus f fInt g gInt).
 apply IntegrablePlusMaj.
Defined.

Definition domainInfiniteSumAbsScaleInc
           {R : ConstructiveReals} (X : Set)
           (fn : nat -> @PartialFunction R X)
           (a : CRcarrier R)
           (x : X)
           (xD : Domain (XinfiniteSumAbs fn) x)
  : { y : Domain (XinfiniteSumAbs (fun n : nat => Xscale a (fn n))) x
    | partialApply _ x y == (partialApply _ x xD) * a }.
Proof.
  destruct xD as [xn cv]; simpl.
  pose proof (CR_complete R _ cv) as [l cvl].
  destruct (domainInfiniteSumAbsInc
              (fun n => Xscale a (fn n)) x
              xn (l * CRabs _ a))
    as [y e].
  - apply (series_cv_eq
             (fun n : nat => CRabs _ (partialApply (fn n) x (xn n)) * CRabs _ a)).
    intro n. rewrite applyXscale. rewrite CRabs_mult.
    apply CRmult_comm. apply series_cv_scale. apply cvl.
  - exists (existT _ y e).
    destruct (series_cv_abs (fun n : nat => a * partialApply (fn n) x (y n)) e).
    destruct (series_cv_abs (fun n : nat => partialApply (fn n) x (xn n)) cv).
    apply (series_cv_unique
             (fun n : nat => (a * partialApply (fn n) x (y n))) _ _ s).
    apply (series_cv_eq (fun n : nat => (partialApply (fn n) x (xn n)) * a)).
    intro n. rewrite CRmult_comm. apply CRmult_morph.
    reflexivity. apply DomainProp. apply series_cv_scale.
    exact s0.
Qed.

Definition domainInfiniteSumAbsScaleIncReverse
           {R : ConstructiveReals} (X : Set)
           (fn : nat -> @PartialFunction R X)
           (a : CRcarrier R)
           (x : X)
           (xD : Domain (XinfiniteSumAbs (fun n : nat => Xscale a (fn n))) x)
           (aNZ : CRapart R a 0)
  : { y : Domain (XinfiniteSumAbs fn) x
      | partialApply _ x y == (partialApply _ x xD) * (CRinv R a aNZ) }.
Proof.
  intros.
  destruct xD as [xn cv]; simpl.
  pose proof (CR_complete R _ cv) as [l cvl].
  destruct (domainInfiniteSumAbsInc
              fn x xn
              (l * CRabs _ (CRinv R a aNZ))) as [y e].
  - apply (series_cv_eq
             (fun n : nat => (CRabs _ (partialApply (Xscale a (fn n)) x
                                            (xn n)) * CRabs _ (CRinv R a aNZ)))).
    intro n. rewrite applyXscale. rewrite CRabs_mult.
    rewrite CRmult_comm, <- CRmult_assoc, <- CRabs_mult, CRinv_l.
    rewrite CRabs_right. rewrite CRmult_1_l. reflexivity.
    apply CRlt_asym, CRzero_lt_one.
    apply series_cv_scale. apply cvl.
  - exists (existT _ y e).
    apply (applyInfiniteSumAbs _ fn x (existT _ y e)).
    apply (series_cv_eq
             (fun n : nat => partialApply (Xscale a (fn n)) x (xn n) * CRinv R a aNZ)).
    intro n. rewrite CRmult_comm. rewrite applyXscale.
    rewrite <- CRmult_assoc. rewrite CRinv_l. rewrite CRmult_1_l.
    apply DomainProp. apply series_cv_scale.
    destruct (series_cv_abs (fun n : nat => a * partialApply (fn n) x (xn n)) cv).
    exact s.
Qed.

Definition IntegralRepresentationWeave {IS : IntegrationSpace}
  (a b : @IntegralRepresentation IS) : @IntegralRepresentation IS.
Proof.
  apply (Build_IntegralRepresentation
           IS
           (weaveSequences _ (IntFn a) (IntFn b))
           (weaveSequencesL (ElemFunc IS) _ (IntFnL a) _ (IntFnL b))
           (IntAbsSum a + IntAbsSum b)).
  apply (series_cv_eq
           (weaveSequences (CRcarrier (RealT (ElemFunc IS)))
                           (fun k => (Iabs (IntFn a k) (IntFnL a k)))
                           (fun k => (Iabs (IntFn b k) (IntFnL b k))))).
  - intro n. unfold weaveSequences, weaveSequencesL.
    destruct (Nat.even n). reflexivity. reflexivity.
  - apply weaveInfiniteSums; apply IntAbsSumCv.
Defined.

Lemma IntegralRepresentationWeaveSum
  : forall {IS : IntegrationSpace}
      (a b : @IntegralRepresentation IS),
      IntegralSeries (IntegralRepresentationWeave a b)
      == IntegralSeries a + IntegralSeries b.
Proof.
  intros.
  apply (series_cv_unique
           (fun n => I IS (IntFn (IntegralRepresentationWeave a b) n)
                    (IntFnL (IntegralRepresentationWeave a b) n) )).
  apply IntegralCv. simpl.
  apply (series_cv_eq
           (weaveSequences (CRcarrier (RealT (ElemFunc IS)))
                           (fun n => I IS (IntFn a n) (IntFnL a n))
                           (fun n => I IS (IntFn b n) (IntFnL b n)))).
  intro n. unfold weaveSequences, weaveSequencesL.
  destruct (Nat.even n); reflexivity.
  apply weaveInfiniteSums; apply IntegralCv.
Qed.

Definition IntegralRepresentationScaleHalf
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (a : CRcarrier (RealT (ElemFunc IS)))
  : IntegrableFunction f
    -> @IntegralRepresentation IS.
Proof.
  intros. destruct X.
  apply (Build_IntegralRepresentation
           IS (fun n:nat => Xscale a (IntFn x n))
           (fun n:nat => LscaleStable _ a (IntFn x n) (IntFnL x n))
           (IntAbsSum x * CRabs _ a)).
  apply (series_cv_eq
           (fun n => (Iabs (IntFn x n) (IntFnL x n)) * CRabs _ a)).
  intro n. rewrite IabsHomogeneous. apply CRmult_comm.
  apply series_cv_scale. apply x.
Defined.

(* If f : X -> R is integrable with representation fn, then
   a*f is integrable with representation a*fn.
   This works even if a is zero, but in this case we must restrict
   the domain of the representation, so that it is that of f :
   we weave fn, -fn with the scaled representation. *)
Definition IntegralRepresentationScale
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (a : CRcarrier (RealT (ElemFunc IS)))
  : IntegrableFunction f
    -> @IntegralRepresentation IS
  := fun X => IntegralRepresentationWeave
           (IntegralRepresentationScaleHalf f a X)
           (IntegralRepresentationWeave
              (let (x,_) := X in x)
              (IntegralRepresentationScaleHalf f (-(1)) X)).

Definition IntegralRepresentationScaleInj
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (a : CRcarrier (RealT (ElemFunc IS)))
           (fInt : IntegrableFunction f)
  : PartialRestriction
      (XinfiniteSumAbs (IntFn (IntegralRepresentationScale f a fInt)))
      (Xscale a f).
Proof.
  split.
  - (* Domain inclusion *)
    intros x xd.
    destruct fInt as [[fn fnL] [injF resF]];
      unfold IntegralRepresentationScale, IntFn in x;
      unfold IntegralRepresentationScale, IntFn;
      simpl in injF, resF.
    (* By subsequence, x is in the domain of abs fn. *)
    pose proof (domainInfinSumWeaveR _ _ _ x xd) as y.
    pose proof (domainInfinSumWeaveL _ _ _ x y) as z.
    exact (injF x z).
  - intros.
    apply (applyInfiniteSumAbs _ _ x).
    destruct fInt as [[fn fnL] [injF resF]];
      unfold IntegralRepresentationScale, IntFn in x;
      unfold IntegralRepresentationScale, IntFn;
      simpl in injF, resF.
    pose proof (domainInfinSumWeaveR _ _ _ x xD) as y.
    pose proof (domainInfinSumWeaveL _ _ _ x y) as z.
    apply (series_cv_eq
           (weaveSequences
              _
              (fun n : nat => (partialApply (fn n) x
                                             (domainInfiniteSumAbsIncReverse _ x z n))
                               * a)
              (weaveSequences
                 _ (fun n : nat => partialApply (fn n) x
                                           (domainInfiniteSumAbsIncReverse _ x z n))
                 (fun n : nat => CRopp _ (partialApply (fn n) x
                                               (domainInfiniteSumAbsIncReverse _ x z n)))))).
    + intro n.
      pose proof (domainInfinSumWeaveL _ _ _ x xD) as t.
      rewrite (partialApplyWeave
                    _ _ _ n x
                    (domainInfiniteSumAbsIncReverse _ x t (n/2))
                    (domainInfiniteSumAbsIncReverse _ x y (n/2))).
      unfold weaveSequences. destruct (Nat.even n).
      rewrite CRmult_comm. rewrite <- applyXscale. apply DomainProp.
      pose proof (partialApplyWeave _ fn (fun n => Xscale (CRopp _ 1) (fn n)) (n/2) x
                 (domainInfiniteSumAbsIncReverse fn x z (n / 2 / 2))
                 (domainInfiniteSumAbsIncReverse
                                     fn x z (n / 2 / 2))).
      rewrite H. destruct (Nat.even (n / 2)). reflexivity.
      rewrite applyXscale. rewrite <- CRopp_mult_distr_l.
      rewrite CRmult_1_l. unfold IntFn. reflexivity.
    + rewrite <- (CRplus_0_r (partialApply (Xscale a f) x xG)).
      rewrite <- (CRplus_opp_r (partialApply (XinfiniteSumAbs fn) x z)).
      apply weaveInfiniteSums. rewrite applyXscale.
      rewrite CRmult_comm. apply series_cv_scale.
      apply applyInfiniteSumAbs. apply resF.
      apply weaveInfiniteSums.
      apply applyInfiniteSumAbs. reflexivity.
      apply series_cv_opp. apply applyInfiniteSumAbs. reflexivity.
Qed.

Definition IntegrableScale {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (a : CRcarrier (RealT (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction (Xscale a f).
Proof.
  intros fInt.
  exists (IntegralRepresentationScale f a fInt).
  exact (IntegralRepresentationScaleInj f a fInt).
Defined.

Lemma minusOneNotZero : forall {R : ConstructiveReals}, CRopp R 1 <> 0.
Proof.
  intros R absurd. pose proof (CRzero_lt_one R).
  apply (CRplus_lt_compat_l _ (CRopp R 1)) in H.
  rewrite CRplus_opp_l, CRplus_0_r in H.
  rewrite absurd in H. exact (CRlt_asym _ _ H H).
Qed.

Definition IntegrableMinus
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (g : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction g
    -> IntegrableFunction (Xminus f g).
Proof.
  intros fInt gInt.
  exact (IntegrablePlus f (Xscale (-(1)) g) fInt
                        (IntegrableScale g (-(1)) gInt)).
Defined.

Lemma splitInfiniteSumMaj
  : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
      (a s : CRcarrier R),
    series_cv u s
    -> a < s
    -> { N : nat | CRltProp R (a + s - CRsum u N) (CRsum u N) }.
Proof.
  intros.
  destruct (Un_cv_nat_real _ s H ((s - a) * CR_of_Q R (1 # 2))) as [N H1].
  + apply CRmult_lt_0_compat. rewrite <- (CRplus_opp_r a).
    apply CRplus_lt_compat_r. exact H0.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
  + exists N. specialize (H1 N (le_refl N)).
    rewrite CRabs_minus_sym in H1.
    apply (CRle_lt_trans (s - CRsum u N)) in H1.
    apply (CRmult_lt_compat_r (CR_of_Q R 2)) in H1.
    rewrite CRmult_assoc in H1.
    rewrite <- CR_of_Q_mult in H1.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q in H1. 2: reflexivity.
    rewrite CR_of_Q_one, CRmult_1_r in H1.
    assert ((s - CRsum u N) * CR_of_Q R 2 == s + s - CRsum u N -CRsum u N).
    { rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l.
      rewrite CRmult_1_r. unfold CRminus. do 3 rewrite CRplus_assoc.
      apply CRplus_morph. reflexivity. rewrite CRplus_comm, CRplus_assoc.
      reflexivity. }
    rewrite H2 in H1. unfold CRminus in H1. apply (CRplus_lt_compat_l _ (-s)) in H1.
    rewrite <- CRplus_assoc, <- CRplus_assoc in H1. rewrite <- CRplus_assoc in H1.
    rewrite CRplus_opp_l in H1. rewrite CRplus_0_l in H1.
    rewrite <- CRplus_assoc in H1. rewrite CRplus_opp_l in H1. rewrite CRplus_0_l in H1.
    apply (CRplus_lt_compat_l _ a) in H1. rewrite CRplus_opp_r in H1.
    apply (CRplus_lt_compat_r (CRsum u N)) in H1. rewrite CRplus_assoc in H1.
    rewrite CRplus_assoc in H1. rewrite CRplus_opp_l in H1. rewrite CRplus_0_r in H1.
    rewrite CRplus_0_l in H1. rewrite <- CRplus_assoc in H1.
    apply CRltForget. assumption. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_lt. reflexivity. apply CRle_abs.
Qed.

Lemma sumPosNegPart : forall {R : ConstructiveReals} (x : CRcarrier R),
    CRabs _ x == (CRmax 0 x) + CRmax 0 (-x).
Proof.
  split.
  - apply (CRplus_le_reg_l (-CRmax 0 x)).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    apply CRmax_lub. apply (CRplus_le_reg_l (CRmax 0 x)).
    rewrite CRplus_0_r, <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    apply CRmax_lub. apply CRabs_pos. apply CRle_abs.
    apply (CRplus_le_reg_l (CRmax 0 x + x)).
    rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    rewrite (CRplus_comm (CRmax 0 x)), CRplus_assoc.
    rewrite <- (CRplus_assoc (CRmax 0 x)), CRplus_opp_r, CRplus_0_l.
    apply CRmax_lub. apply (CRplus_le_reg_l (-x)).
    rewrite CRplus_0_r, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    rewrite <- CRabs_opp. apply CRle_abs.
    rewrite <- (CRplus_0_r x). rewrite CRplus_assoc.
    apply CRplus_le_compat_l. rewrite CRplus_0_l. apply CRabs_pos.
  - apply CRabs_le. split.
    + apply (CRplus_le_reg_l (CRmax 0 (-x) - x)).
      unfold CRminus. rewrite CRplus_assoc, CRplus_assoc, CRplus_opp_l.
      rewrite CRplus_0_r. rewrite <- CRplus_assoc, (CRplus_comm), CRopp_plus_distr.
      rewrite CRplus_assoc, <- (CRplus_assoc (-CRmax 0 (-x))).
      rewrite CRplus_opp_l, CRplus_0_l.
      apply (CRle_trans _ (-x)). 2: apply CRmax_r.
      apply (CRplus_le_reg_l (CRmax 0 x)).
      rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
      rewrite <- (CRplus_0_l (-x)), <- CRplus_assoc. apply CRplus_le_compat_r.
      rewrite CRplus_0_r. apply CRmax_l.
    + apply (CRle_trans _ (x + CRmax 0 (-x))).
      rewrite <- (CRplus_0_r x). rewrite CRplus_assoc.
      apply CRplus_le_compat_l. rewrite CRplus_0_l.
      apply CRmax_l. apply CRplus_le_compat. apply CRmax_r.
      apply CRle_refl.
Qed.

Lemma minusPosNegPart : forall {R : ConstructiveReals} (x : CRcarrier R),
    x == (CRmax 0 x) - (CRmax 0 (-x)).
Proof.
  split.
  - apply (CRplus_le_reg_l (CRmax 0 (-x))).
    rewrite CRplus_comm. unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    apply CRmax_lub. apply (CRplus_le_reg_l (-x)).
    rewrite CRplus_0_r, CRplus_comm, CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    apply CRmax_r. apply (CRplus_le_reg_l (-x)).
    rewrite CRplus_opp_l, CRplus_comm, CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    apply CRmax_l.
  - apply (CRplus_le_reg_l (CRmax 0 (-x) - x)).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite CRplus_comm, CRplus_assoc, <- (CRplus_assoc (-CRmax 0 (-x))).
    rewrite CRplus_opp_l, CRplus_0_l.
    apply CRmax_lub. apply (CRplus_le_reg_l x).
    rewrite CRplus_0_r, CRplus_comm, CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    apply CRmax_r.
    rewrite <- (CRplus_0_l (-x)). rewrite <- CRplus_assoc.
    apply CRplus_le_compat_r. rewrite CRplus_0_r. apply CRmax_l.
Qed.

Lemma infiniteSumPosNegParts
  : forall {R : ConstructiveReals} (X : Set)
      (fn : nat -> PartialFunction X)
      (x : X)
      (xn : forall n:nat, Domain (fn n) x)
      (pos neg : CRcarrier R),
    series_cv (fun n => CRmax 0 (partialApply (fn n) x (xn n))) pos
    -> series_cv (fun n => CRmax 0 (- partialApply (fn n) x (xn n))) neg
    -> series_cv (fun n => partialApply (fn n) x (xn n)) (pos - neg).
Proof.
  intros. apply (series_cv_scale (-(1)) neg) in H0.
  apply (series_cv_plus (fun n : nat => CRmax 0 (partialApply (fn n) x (xn n)))
                           (fun n : nat =>
                              (CRmax 0 (- partialApply (fn n) x (xn n)) * -(1)))
        pos (neg * -(1)) H) in H0. assert (pos + neg * -(1) == pos - neg).
  rewrite <- CRopp_mult_distr_r, CRmult_1_r. reflexivity.
  rewrite H1 in H0. apply (series_cv_eq (fun n : nat =>
          (CRmax 0 (partialApply (fn n) x (xn n)) +
           CRmax 0 (- partialApply (fn n) x (xn n)) * -(1)))
                                             (fun n : nat => partialApply (fn n) x (xn n))).
  intro n. rewrite <- (CRopp_mult_distr_r _ 1). rewrite CRmult_1_r.
  symmetry. apply minusPosNegPart. apply H0.
Qed.

Lemma splitSumAbsPosNeg
  : forall {R : ConstructiveReals} (X : Set)
      (fn : nat -> PartialFunction X)
      (x : X)
      (xn : forall n:nat, Domain (fn n) x)
      (A : CRcarrier R),
    series_cv (fun n => CRabs _ (partialApply (fn n) x (xn n))) A
    -> prod { pos : CRcarrier R &
                    prod (pos <= A)
                         (series_cv (fun n => CRmax 0 (partialApply (fn n) x (xn n))) pos) }
            { neg : CRcarrier R &
                    prod (neg <= A)
                         (series_cv (fun n => CRmax 0 (- partialApply (fn n) x (xn n))) neg) }.
Proof.
  intros. split.
  - destruct (series_cv_maj
                (fun n => CRmax 0 (partialApply (fn n) x (xn n)))
                (fun n : nat => CRabs _ (partialApply (fn n) x (xn n)))
                A) as [l cvl].
    intro n. simpl. rewrite CRabs_right.
    apply CRmax_lub. apply CRabs_pos.
    apply CRle_abs. apply CRmax_l.
    assumption. exists l. split; apply cvl.
  - destruct (series_cv_maj
                (fun n => CRmax 0 (- partialApply (fn n) x (xn n)))
                (fun n : nat => CRabs _ (partialApply (fn n) x (xn n)))
                A) as [l cvl].
    intro n. simpl.
    rewrite CRabs_right. apply CRmax_lub. apply CRabs_pos.
    rewrite <- CRabs_opp. apply CRle_abs. apply CRmax_l.
    assumption. exists l. split; apply cvl.
Qed.

Lemma applyPlusTruncated
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (n M : nat)
      (x : X (ElemFunc IS))
      (pF : Domain f x)
      (pS : Domain (Xplus (XposPart f)
                          (if le_dec n M then Izero IS
                           else XnegPart f)) x),
    partialApply _ x pS
    == (CRmax 0 (partialApply f x pF)
       + (if le_dec n M then 0
          else CRmax 0 (- partialApply f x pF))).
Proof.
  intros. destruct (le_dec n M).
  - rewrite CRplus_0_r. destruct pS.
    rewrite (applyXplus (XposPart f) (Izero IS)).
    unfold Izero. rewrite applyXscale, CRmult_0_l.
    rewrite <- (DomainProp (XposPart f) x (pF, pF)).
    rewrite applyXposPart. rewrite CRplus_0_r. reflexivity.
  - destruct pS. rewrite (applyXplus (XposPart f) (XnegPart f)).
    apply CRplus_morph.
    rewrite <- (DomainProp (XposPart f) x (pF, pF)).
    rewrite applyXposPart. reflexivity.
    rewrite <- (DomainProp (XnegPart f) x (pF, pF)).
    rewrite applyXnegPart. reflexivity.
Qed.

Lemma splitIntegralPosNeg
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fL : L (ElemFunc IS) f),
    I IS f fL
    == (I IS (XposPart f) (LposPartStable f fL))
       - (I IS (XnegPart f) (LnegPartStable f fL)).
Proof.
  intros. rewrite <- (CRmult_1_l (I IS (XnegPart f) (LnegPartStable f fL))).
  unfold CRminus. rewrite CRopp_mult_distr_l. rewrite <- Ihomogeneous.
  rewrite <- Iadditive. apply IExtensional. intros.
  destruct y.
  rewrite (applyXplus (XposPart f) (Xscale (- (1)) (XnegPart f))).
  rewrite applyXscale.
  unfold XposPart, XnegPart. do 2 rewrite applyXscale.
  destruct d. rewrite (applyXplus f (Xabs f) x).
  destruct d0. rewrite (applyXminus (Xabs f) f).
  do 2 rewrite applyXabs.
  rewrite (DomainProp f x d1 d), (DomainProp f x d2 d),
  (DomainProp f x d0 d), (DomainProp f x xF d).
  generalize (partialApply f x d). intros.
  rewrite <- CRopp_mult_distr_l, CRmult_1_l.
  rewrite CRopp_mult_distr_r, <- CRmult_plus_distr_l.
  setoid_replace (c + CRabs _ c + - (CRabs _ c + - c))
    with (CR_of_Q _ 2 * c).
  rewrite <- CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q.
  rewrite CR_of_Q_one, CRmult_1_l. reflexivity. reflexivity.
  rewrite (CR_of_Q_plus _ 1 1), CR_of_Q_one, CRmult_plus_distr_r.
  rewrite CRmult_1_l, CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite CRopp_plus_distr, <- CRplus_assoc, CRplus_opp_r.
  rewrite CRplus_0_l, CRopp_involutive. reflexivity.
Qed.

Lemma splitIntegralSumPosNeg
  : forall {IS : IntegrationSpace}
      (fn : nat -> PartialFunction (X (ElemFunc IS)))
      (fnL : forall n:nat, L (ElemFunc IS) (fn n))
      (sumAbsIFn : CRcarrier (RealT (ElemFunc IS))),
    (series_cv (fun n => Iabs (fn n) (fnL n)) sumAbsIFn)
    -> { sumIPosFn : CRcarrier _ & { sumINegFn : CRcarrier _ &
      series_cv (fun n0 : nat =>
                      I IS (XposPart (fn n0))
                        (LposPartStable (fn n0) (fnL n0))) sumIPosFn
      * series_cv (fun n0 : nat =>
                      I IS (XnegPart (fn n0))
                        (LnegPartStable (fn n0) (fnL n0))) sumINegFn
      * series_cv (fun n => I IS (fn n) (fnL n)) (sumIPosFn - sumINegFn) }}%type.
Proof.
  intros. (* The sum of I fn+ converges *)
  destruct (series_cv_maj
              (fun n0 : nat =>
                 I IS (XposPart (fn n0))
                   (LposPartStable (fn n0) (fnL n0)))
              (fun n0 : nat => Iabs (fn n0) (fnL n0))
              sumAbsIFn) as [sumIPosFn [limPos _]].
  { intro n.
    apply (CRle_trans _ (Iabs (XposPart (fn n)) (LposPartStable (fn n) (fnL n)))).
    apply integralAbsMaj. apply INonDecreasing. intros.
    rewrite applyXabs, CRabs_right.
    2: apply applyXposPartNonNeg.
    rewrite <- (DomainProp (XposPart (fn n)) x (y, y)).
    rewrite (applyXposPart (fn n)). rewrite applyXabs.
    apply CRmax_lub. apply CRabs_pos. apply CRle_abs. }
  assumption.

  (* The sum of I fn- converges *)
  destruct (series_cv_maj
              (fun n0 : nat =>
                 I IS (XnegPart (fn n0))
                   (LnegPartStable (fn n0) (fnL n0)))
              (fun n0 : nat => Iabs (fn n0) (fnL n0))
              sumAbsIFn) as [sumINegFn [limNeg _]].
  { intro n.
    apply (CRle_trans _ (Iabs (XnegPart (fn n)) (LnegPartStable  (fn n) (fnL n)))).
    apply integralAbsMaj. apply INonDecreasing. intros.
    rewrite applyXabs, CRabs_right.
    2: apply XnegPartNonNeg.
    rewrite <- (DomainProp (XnegPart (fn n)) x (y,y)).
    rewrite (applyXnegPart (fn n)). rewrite applyXabs.
    apply CRmax_lub. apply CRabs_pos.
    rewrite <- CRabs_opp. apply CRle_abs. }
  apply H.

  exists sumIPosFn. exists sumINegFn. repeat split. assumption. assumption.
  apply (series_cv_scale (-(1)) sumINegFn) in limNeg.
  apply (series_cv_plus (fun n0 : nat =>
              I IS (XposPart (fn n0))
                (LposPartStable (fn n0) (fnL n0)))
                           (fun n : nat =>
              (I IS (XnegPart (fn n))
                 (LnegPartStable (fn n) (fnL n)) * -(1)))
        sumIPosFn (sumINegFn * -(1)) limPos)
        in limNeg.
  apply (series_cv_eq (fun n : nat =>
              (I IS (XposPart (fn n))
                 (LposPartStable (fn n) (fnL n)) +
               I IS (XnegPart (fn n))
                 (LnegPartStable (fn n) (fnL n)) * -(1)))
                         (fun n : nat => I IS (fn n) (fnL n)))
        in limNeg.
  apply (CR_cv_proper _ (sumIPosFn + sumINegFn * - (1))).
  exact limNeg. rewrite <- CRopp_mult_distr_r, CRmult_1_r. reflexivity.
  intro n.
  assert ((I IS (XposPart (fn n))
     (LposPartStable (fn n) (fnL n)) +
   I IS (XnegPart (fn n))
     (LnegPartStable (fn n) (fnL n)) * -(1))
          == (I IS (XposPart (fn n))
     (LposPartStable (fn n) (fnL n)) -
   I IS (XnegPart (fn n))
     (LnegPartStable (fn n) (fnL n)))).
  rewrite <- CRopp_mult_distr_r, CRmult_1_r. reflexivity.
  rewrite H0. clear H0. rewrite <- splitIntegralPosNeg. reflexivity.
Qed.

Definition domainPlusPosPartInc {R : ConstructiveReals} (X : Set)
           (f g : @PartialFunction R  X)
           (x : X)
           (xD : Domain (Xplus (XposPart f) g) x)
  : Domain f x.
Proof.
  destruct f,g,xD; simpl. exact (fst d).
Qed.

(* Workaround destruct that no longer works *)
Lemma series_cv_abs_le
  : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (a : CRcarrier R)
      (cau : CR_cauchy R (CRsum (fun n => CRabs R (un n)))),
    CRle R a (let (c,_) := series_cv_abs un cau in c)
    -> { l : CRcarrier R & prod (CRle R a l) (series_cv un l) }.
Proof.
  intros. destruct (series_cv_abs un cau). exists x.
  split; assumption.
Qed.

(* This is the generalization of INonDecreasing
   from L-functions to integrable functions. *)
Lemma representationPositive
  : forall {IS : IntegrationSpace}
      (fInt : @IntegralRepresentation IS),
    nonNegFunc (XinfiniteSumAbs (IntFn fInt))
    -> 0 <= IntegralSeries fInt.
Proof.
  (* To use Icontinuity, we fallback to positive functions
     by taking XposParts and XnegParts. *)
  intros IS [fn fnL sumAbsIFn H] H0.
  destruct (splitIntegralSumPosNeg fn fnL sumAbsIFn H)
    as [sumIPosFn [sumINegFn [[limPos limNeg] splitIntegral]]].
  setoid_replace (IntegralSeries {| IntFn := fn; IntFnL := fnL; IntAbsSum := sumAbsIFn; IntAbsSumCv := H |})
    with (sumIPosFn - sumINegFn).

  rewrite <- (CRplus_opp_r sumINegFn).
  apply CRplus_le_compat. 2: apply CRle_refl. intro absurd.

  (* Truncate XinfiniteSumAbs _ (fun n:nat => XnegPart _ (fn n))
     to a finite sum, to keep an L-function. *)
  destruct (splitInfiniteSumMaj (fun n : nat =>
                                   I IS (XnegPart (fn n))
                                     (LnegPartStable (fn n) (fnL n)))
                                sumIPosFn sumINegFn limNeg)
    as [M H1].
  assumption.

  destruct
    (Icontinuous IS
                 (Xsum (fun n:nat => XnegPart (fn n)) M)
                 (fun n:nat => Xplus (XposPart (fn n))
                                match le_dec n M with
                                | left _ => Izero IS
                                | _ => XnegPart (fn n)
                                end)
                 (LsumStable (fun n : nat => XnegPart (fn n))
                             (fun n => LnegPartStable (fn n) (fnL n))
                             M)
                 (fun n:nat => LplusStable (ElemFunc IS)
                                      (XposPart (fn n))
                                      (match le_dec n M with
                                       | left _ => Izero IS
                                       | _ => XnegPart (fn n)
                                       end)
                                      (LposPartStable (fn n) (fnL n))
                                      (if le_dec n M as s return (L (ElemFunc IS) (if s then Izero IS else XnegPart (fn n)))
                                       then
                                         Izero_is_L IS
                                       else LnegPartStable (fn n) (fnL n)))
    )
    as [[x xS xdfn] [sumPosNegFX [H2 H3]]].
  - (* non neg func *)
    intros. intros z xdf.
    destruct (le_dec n M). destruct xdf.
    rewrite (applyXplus (XposPart (fn n)) (Izero IS)), <- (CRplus_0_r 0).
    apply CRplus_le_compat. apply applyXposPartNonNeg.
    rewrite applyIzero. apply CRle_refl. destruct xdf.
    rewrite (applyXplus (XposPart (fn n)) (XnegPart (fn n))), <- (CRplus_0_r 0).
    apply CRplus_le_compat. apply applyXposPartNonNeg.
    apply XnegPartNonNeg.
  - (* limit lt *)
    exists (sumIPosFn + (sumINegFn
                    - CRsum
                        (fun n : nat =>
                           I IS (XnegPart (fn n))
                             (LnegPartStable (fn n) (fnL n))) M)).
    split.
    + apply (series_cv_eq
               (fun n : nat => I IS (XposPart (fn n))
                            (LposPartStable (fn n) (fnL n))
                          + (I IS (if le_dec n M then Izero IS else XnegPart (fn n))
                                   (if le_dec n M as s
                                       return (L (ElemFunc IS) (if s then Izero IS else XnegPart (fn n)))
                                    then Izero_is_L IS
                                    else LnegPartStable (fn n) (fnL n))))).
      intros. rewrite Iadditive. reflexivity.
      apply series_cv_plus. assumption.
      apply (series_cv_eq (fun n : nat =>
                                if le_dec n M then 0
                                else I IS (XnegPart (fn n))
                                       (LnegPartStable (fn n) (fnL n)))).
      intros. destruct (le_dec n M). rewrite Izero_is_zero. reflexivity. reflexivity.
      apply infinite_sum_truncate_below. assumption.
    + rewrite IadditiveIterate. unfold CRminus.
      rewrite <- CRplus_assoc. apply CRltEpsilon. assumption.
  - (* Now we have x, prove that sum |fn x| converges. *)
    pose proof (fun n:nat => domainPlusPosPartInc _ _ _ x (xdfn n)) as pxn.

    (* Simplify H2 *)
    apply (series_cv_eq (fun n : nat =>
                      partialApply
            (Xplus (XposPart (fn n))
               (if le_dec n M then Izero IS else XnegPart (fn n))) x
            (xdfn n))
                           (fun n : nat =>
                              CRmax 0 (partialApply (fn n) x (pxn n))
                              + (if le_dec n M then 0
                                     else CRmax 0 (- partialApply (fn n) x (pxn n)))))
      in H2.
    assert (series_cv (fun n : nat =>
                            (if le_dec n M then CRmax 0 (- partialApply (fn n) x (pxn n))
                             else 0))
                         (CRsum (fun k => CRmax 0 (- partialApply (fn k) x (pxn k))) M)).
    { intros eps. exists M. intros. rewrite sum_truncate_above.
      unfold CRminus. rewrite CRplus_opp_r.
      rewrite CRabs_right. rewrite <- CR_of_Q_zero. apply CR_of_Q_le.
      discriminate. apply CRle_refl. exact H4. }
    apply (series_cv_plus (fun n : nat =>
          (CRmax 0 (partialApply (fn n) x (pxn n)) +
           (if le_dec n M then 0 else CRmax 0 (- partialApply (fn n) x (pxn n)))))
                               (fun n : nat =>
          if le_dec n M then CRmax 0 (- partialApply (fn n) x (pxn n)) else 0)
                               sumPosNegFX (CRsum (fun k => CRmax 0 (- partialApply (fn k) x (pxn k))) M)
                               H2)
        in H4.
    apply (series_cv_eq (fun n : nat =>
          (CRmax 0 (partialApply (fn n) x (pxn n)) +
           (if le_dec n M then 0 else CRmax 0 (- partialApply (fn n) x (pxn n))) +
           (if le_dec n M then CRmax 0 (- partialApply (fn n) x (pxn n)) else 0)))
                             (fun n : nat => CRabs _ (partialApply (fn n) x (pxn n))))
        in H4.

    (* Deduce that sum fn x >= 0 *)
    unfold nonNegFunc in H0.
    pose proof (domainInfiniteSumAbsInc fn x pxn
               (sumPosNegFX +
                CRsum (fun k : nat => CRmax 0 (- partialApply (fn k) x (pxn k))) M)
               H4)
      as y.
    specialize (H0 x y). destruct y as [yn ycv]; simpl in H0.
    apply series_cv_abs_le in H0. destruct H0 as [sumFX [H0 i]].

    destruct (splitSumAbsPosNeg _ fn x pxn
                                    (sumPosNegFX +
                                     CRsum (fun k : nat => CRmax 0 (- partialApply (fn k) x (pxn k))) M)
                                    H4) as [H6 H7].
    destruct H6 as [sumPosFnX [H6 limPosX]].
    destruct H7 as [sumNegFnX [H7 limNegX]].

    assert (sumPosFnX < sumNegFnX).
    { apply (CRle_lt_trans sumPosFnX sumPosNegFX).
      apply (series_cv_scale (-(1)) sumPosFnX) in limPosX.
      apply (series_cv_plus (fun n : nat =>
          (CRmax 0 (partialApply (fn n) x (pxn n)) +
           (if le_dec n M then 0 else CRmax 0 (- partialApply (fn n) x (pxn n)))))
                                 (fun n : nat => (CRmax 0 (partialApply (fn n) x (pxn n)) * -(1)))
              sumPosNegFX (sumPosFnX * -(1)))
        in limPosX.
      apply series_cv_nonneg in limPosX.
      assert (sumPosFnX * (-(1)) == - sumPosFnX) as H8.
      rewrite <- CRopp_mult_distr_r, CRmult_1_r. reflexivity.
      rewrite H8 in limPosX. apply (CRplus_le_compat_l sumPosFnX) in limPosX.
      simpl in limPosX. unfold CRminus in limPosX.
      rewrite CRplus_0_r, CRplus_comm, CRplus_assoc, CRplus_opp_l, CRplus_0_r
        in limPosX.
      exact limPosX.
      intro n. assert (CRmax 0 (partialApply (fn n) x (pxn n)) +
   (if le_dec n M then 0 else CRmax 0 (- partialApply (fn n) x (pxn n))) +
   CRmax 0 (partialApply (fn n) x (pxn n)) * -(1)
                         == (if le_dec n M then 0 else CRmax 0 (- partialApply (fn n) x (pxn n)))) as H8.
      rewrite <- CRopp_mult_distr_r, CRmult_1_r, CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
      rewrite H8. destruct (le_dec n M). apply CRle_refl.
      apply CRmax_l. assumption.
      apply (CRlt_le_trans sumPosNegFX (partialApply
          (Xsum (fun n : nat => XnegPart (fn n)) M) x xS)).
      assumption.

      pose proof (fun n:nat => pair (pxn n) (pxn n)) as pxnn.
      rewrite (applyXsum (fun n : nat => XnegPart (fn n)) M x _ pxnn).
      rewrite <- (CRsum_eq (fun n:nat => CRmax 0 (- partialApply (fn n) x (pxn n)))).
      apply growing_ineq. intros p. simpl.
      rewrite <- CRplus_0_r, CRplus_assoc. apply CRplus_le_compat_l.
      rewrite CRplus_0_l.
      apply CRmax_l. assumption. intros.
      rewrite <- (applyXnegPart (fn i0)). apply DomainProp. }

    assert (sumFX == sumPosFnX - sumNegFnX).
    { apply (CR_cv_unique (CRsum (fun k : nat => partialApply (fn k) x (pxn k)))).
      apply (series_cv_eq (fun k : nat => partialApply (fn k) x (yn k))).
      intro n. apply DomainProp. apply i.
      apply infiniteSumPosNegParts. assumption. assumption. }
    rewrite H8 in H0.
    apply (CRplus_le_compat_l sumNegFnX) in H0.
    unfold CRminus in H0.
    rewrite CRplus_0_r, CRplus_comm, CRplus_assoc, CRplus_opp_l, CRplus_0_r in H0.
    apply H0. assumption.

    intros. destruct (le_dec n M). rewrite sumPosNegPart.
    rewrite CRplus_0_r. reflexivity.
    rewrite sumPosNegPart. rewrite CRplus_0_r.
    reflexivity. intro n. apply applyPlusTruncated.
  - apply (CR_cv_unique (CRsum (fun n : nat => I IS (fn n) (fnL n)))).
    simpl.
    destruct (series_cv_maj (fun n : nat => I IS (fn n) (fnL n)) (fun k : nat => Iabs (fn k) (fnL k))
                            sumAbsIFn (fun n : nat => integralAbsMaj (fn n) (fnL n)) H).
    apply p. assumption.
Qed.

Lemma IntegralNonNeg : forall {IS : IntegrationSpace}
                         (f : PartialFunction (X (ElemFunc IS)))
                         (fInt : IntegrableFunction f),
    nonNegFunc f
    -> 0 <= Integral fInt.
Proof.
  intros. apply representationPositive.
  destruct fInt, p. intros y ydf.
  rewrite (c y ydf (d y ydf)). apply H.
Qed.

Lemma IntegralHomogeneousHalf
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a : CRcarrier (RealT (ElemFunc IS))),
    IntegralSeries (IntegralRepresentationScaleHalf f a fInt)
    == (Integral fInt) * a.
Proof.
  intros. destruct fInt.
  apply (series_cv_unique (fun n0 : nat => (I IS (IntFn x n0) (IntFnL x n0)) * a)).
  - apply (series_cv_eq (fun n:nat => I IS (Xscale a (IntFn x n))
                                      (LscaleStable _ a _ (IntFnL x n)))).
    intro n. rewrite Ihomogeneous. apply CRmult_comm.
    apply (IntegralCv (IntegralRepresentationScaleHalf f a
          (existT
             (fun fInt : IntegralRepresentation =>
              PartialRestriction (XinfiniteSumAbs (IntFn fInt)) f) x p))).
  - apply series_cv_scale. simpl. apply (IntegralCv x).
Qed.

Lemma IntegralScale
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (a : CRcarrier (RealT (ElemFunc IS))),
    Integral (IntegrableScale f a fInt)
    == (Integral fInt) * a.
Proof.
  intros.
  unfold IntegrableScale, IntegralRepresentationScale, Integral.
  do 2 rewrite IntegralRepresentationWeaveSum.
  do 2 rewrite IntegralHomogeneousHalf. unfold Integral.
  rewrite <- CRopp_mult_distr_r, CRmult_1_r, CRplus_opp_r.
  rewrite CRplus_0_r. reflexivity.
Qed.

(* Base result to prove that integral is extensional *)
Lemma IntegralRepresentationInvariantZero
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
    (forall (x : X (ElemFunc IS)) (xD : Domain f x),
        partialApply f x xD == 0)
    -> Integral fInt == 0.
Proof.
  intros. split.
  - apply representationPositive.
    intros x xdf. destruct fInt,p. rewrite (c x _ (d x xdf)).
    rewrite H. apply CRle_refl.
  - setoid_replace (Integral fInt)
      with (CRopp _ (IntegralSeries (IntegralRepresentationScale _ (-(1)) fInt))).
    rewrite <- CRopp_0. apply CRopp_ge_le_contravar.
    apply representationPositive.
    intros x xdf.
    destruct (IntegralRepresentationScaleInj f (-(1)) fInt).
    rewrite (c x xdf (d x xdf)).
    rewrite applyXscale, H. rewrite CRmult_0_r. apply CRle_refl.
    pose proof (IntegralScale f fInt (-(1))).
    rewrite H0. rewrite <- CRopp_mult_distr_r, CRmult_1_r, CRopp_involutive.
    reflexivity.
Qed.

Lemma IntegralOpp
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
    Integral (IntegrableScale f (-(1)) fInt)
    == - Integral fInt.
Proof.
  intros. rewrite IntegralScale.
  rewrite <- CRopp_mult_distr_r, CRmult_1_r. reflexivity.
Qed.

Lemma IntegralPlus
  : forall {IS : IntegrationSpace}
      (f g : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (gInt : IntegrableFunction g),
    Integral (IntegrablePlus f g fInt gInt)
    == Integral fInt + Integral gInt.
Proof.
  intros.
  destruct (IntegrablePlus f g fInt gInt)
    as [[pn pnL IsumP majP] restrictP] eqn:desP.
  destruct fInt as [[fn fnL IsumF majF] restrictF].
  destruct gInt as [[gn gnL IsumG majG] restrictG].
  simpl.
  apply (series_cv_unique
           (weaveSequences _ (fun n0 : nat => I IS (fn n0) (fnL n0))
                           (fun n0 : nat => I IS (gn n0) (gnL n0)))).
  simpl in desP.
  - (* Prove that weaved sequences converges to IntegrablePlus *)
    apply (series_cv_eq (fun n : nat => I IS (pn n) (pnL n))).
    + intro n. unfold IntegrablePlus in desP; simpl in desP.
      inversion desP. inversion H1. unfold weaveSequences, weaveSequencesL.
      destruct (Nat.even n); reflexivity.
    + pose proof (IntegralCv
          {| IntFn := pn; IntFnL := pnL; IntAbsSum := IsumP; IntAbsSumCv := majP |}).
      assumption.
  - apply weaveInfiniteSums.
    + pose proof (IntegralCv
          {| IntFn := fn; IntFnL := fnL; IntAbsSum := IsumF; IntAbsSumCv := majF |}).
      assumption.
    + pose proof (IntegralCv
          {| IntFn := gn; IntFnL := gnL; IntAbsSum := IsumG; IntAbsSumCv := majG |}).
      assumption.
Qed.

Lemma IntegralMinus
  : forall {IS : IntegrationSpace}
      (f g : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (gInt : IntegrableFunction g),
    Integral (IntegrableMinus f g fInt gInt)
    == Integral fInt - Integral gInt.
Proof.
  intros. unfold Xminus. unfold IntegrableMinus.
  rewrite IntegralPlus. rewrite IntegralScale.
  apply CRplus_morph. reflexivity.
  rewrite <- CRopp_mult_distr_r, CRmult_1_r. reflexivity.
Qed.


(* We now come to the invariance of the integral with respect to
   the representation of a function f.

   In addition, this shows that a countable intersection of
   L-functions is also defined almost everywhere : otherwise another
   representation defined at more points could change the integral. *)

Lemma IntegralRepresentationInvariant
      : forall {IS : IntegrationSpace}
          (f : PartialFunction (X (ElemFunc IS)))
          (fnInt gnInt : IntegrableFunction f),
    Integral fnInt == Integral gnInt.
Proof.
  intros.
  assert (forall (x : X (ElemFunc IS)) (xD : Domain (Xplus f (Xscale (-(1)) f)) x),
             partialApply (Xplus f (Xscale (-(1)) f)) x xD == 0).
  { intros. destruct xD.
    rewrite (applyXplus f (Xscale (- (1)) f)), applyXscale.
    rewrite (DomainProp f x d d0), <- CRopp_mult_distr_l, CRmult_1_l.
    apply CRplus_opp_r. }
  pose proof (IntegralRepresentationInvariantZero
                (Xminus f f)
                (IntegrableMinus f f fnInt gnInt)
                H)
    as invZero.
  rewrite IntegralMinus in invZero.
  apply (CRplus_eq_reg_l (-Integral gnInt)).
  rewrite CRplus_opp_l, CRplus_comm. exact invZero.
Qed.

Lemma IntegrableMinusMaj
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (g : PartialFunction (X (ElemFunc IS)))
      (gInt : IntegrableFunction g),
    PartialRestriction (XinfiniteSumAbs (IntFn (let (i,_) := IntegrableMinus f g fInt gInt in i)))
                       (Xminus f g).
Proof.
  intros. apply IntegrablePlusMaj.
Qed.

Lemma IntegralNonDecreasing
  : forall {IS : IntegrationSpace}
      (f g : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (gInt : IntegrableFunction g),
    partialFuncLe f g
    -> Integral fInt <= Integral gInt.
Proof.
  intros.
  pose proof (IntegralMinus g f gInt fInt) as intAdd.
  apply (CRplus_le_reg_r (- Integral fInt)).
  rewrite CRplus_opp_r, <- intAdd.
  clear intAdd. apply representationPositive.
  intros x xdf.
  destruct (IntegrableMinusMaj g gInt f fInt).
  rewrite (c x xdf (d x xdf)).
  destruct (d x xdf). rewrite (applyXminus g f).
  rewrite <- (CRplus_opp_r (partialApply f x d1)).
  apply CRplus_le_compat. apply H. apply CRle_refl.
Qed.

Lemma IntegralExtensional
  : forall {IS : IntegrationSpace}
      (f g : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (gInt : IntegrableFunction g),
    (forall (x : X (ElemFunc IS)) (xdf : Domain f x) (xdg : Domain g x),
        partialApply f x xdf == partialApply g x xdg)
    -> Integral fInt == Integral gInt.
Proof.
  split.
  - apply IntegralNonDecreasing. intros x xdf xdg.
    rewrite (H x xdg xdf). apply CRle_refl.
  - apply IntegralNonDecreasing. intros x xdf xdg.
    rewrite (H x xdf xdg). apply CRle_refl.
Qed.

Definition telescopicOp {R : ConstructiveReals} (X : Set)
           (fn : nat -> PartialFunction X)
           (op : CRcarrier R -> CRcarrier R)
           (opEq : forall x y : CRcarrier R, x == y -> op x == op y)
  := fun n:nat => match n with
             | O => Xop X (fn O) op opEq
             | S p => Xminus (Xop X (Xsum fn n) op opEq)
                            (Xop X (Xsum fn p) op opEq)
             end.

Lemma telescopicOpL : forall {IS : IntegrationSpace}
                        (fn : nat -> PartialFunction (X (ElemFunc IS)))
                        (fnL : forall n:nat, L (ElemFunc IS) (fn n))
                        (op : CRcarrier (RealT (ElemFunc IS))
                              -> CRcarrier (RealT (ElemFunc IS)))
                        (opEq : forall x y : CRcarrier (RealT (ElemFunc IS)),
                            x == y -> op x == op y)
                        (opL : forall f : PartialFunction (X (ElemFunc IS)),
                            L (ElemFunc IS) f -> L (ElemFunc IS) (Xop _ f op opEq))
                        (n : nat),
    L (ElemFunc IS) (telescopicOp (X (ElemFunc IS)) fn op opEq n).
Proof.
  intros. unfold telescopicOp. destruct n. apply (*LabsStable*) opL. apply fnL.
  unfold Xminus. apply LplusStable. apply opL. apply LsumStable. apply fnL.
  apply LscaleStable. apply opL. apply LsumStable. apply fnL.
Defined.

Lemma applyTelescopicOpMaj
  : forall {R : ConstructiveReals} (X : Set)
      (fn : nat -> PartialFunction X)
      (op : CRcarrier R -> CRcarrier R)
      (opEq : forall x y : CRcarrier R, x == y -> op x == op y)
      (contract : forall x y : CRcarrier R,
          (CRabs _ (op x - op y)) <= (CRabs _ (x - y)))
      (zeroFix : op 0 == 0)
      (n : nat)
      (x : X)
      (pF : Domain (fn n) x)
      (pXT : Domain (telescopicOp X fn op opEq n) x),
    CRabs _ (partialApply (telescopicOp X fn op opEq n) x pXT)
    <= CRabs _ (partialApply (fn n) x pF).
Proof.
  intros. unfold telescopicOp. unfold telescopicOp in pXT. destruct n.
  - destruct (fn O); simpl.
    rewrite <- (CRplus_0_r (partialApply x pF)).
    rewrite <- CRopp_0.
    rewrite <- (DomainProp x pXT pF).
    setoid_replace (op (partialApply x pXT)) with (op (partialApply x pXT) - op 0).
    apply contract. rewrite zeroFix. unfold CRminus.
    rewrite CRopp_0, CRplus_0_r. reflexivity.
  - simpl in pXT. destruct pXT.
    rewrite (applyXminus (Xop X (Xsum fn (S n)) op opEq)
                         (Xop X (Xsum fn n) op opEq)).
    simpl.
    apply (CRle_trans _ _ _ (contract _ _)).
    destruct p. simpl.
    destruct (Xsum fn n), (fn (S n)); simpl.
    rewrite (DomainProp x d0 d), (DomainProp0 x pF d1).
    apply (CRle_trans
             _ (CRabs _ ((partialApply x d + partialApply0 x d1) - partialApply x d))).
    apply CRle_refl.
    rewrite CRplus_comm. unfold CRminus. rewrite CRplus_assoc.
    rewrite CRplus_opp_r. rewrite CRplus_0_r. apply CRle_refl.
Qed.

Lemma applyTelescopicOp : forall {R : ConstructiveReals} (X : Set)
                            (fn : nat -> PartialFunction X)
                            (op : CRcarrier R -> CRcarrier R)
                            (opEq : forall x y : CRcarrier R, x == y -> op x == op y)
                            (n : nat)
                            (x : X)
                            (pF : forall n:nat, Domain (fn n) x)
                            (pXT : forall n:nat, Domain (telescopicOp X fn op opEq n) x),
    partialApply (telescopicOp X fn op opEq (S n)) x (pXT (S n))
    == op (CRsum (fun n=> partialApply (fn n) x (pF n)) (S n))
       - op (CRsum (fun n=> partialApply (fn n) x (pF n)) n).
Proof.
  intros. unfold telescopicOp. destruct (pXT (S n)).
  rewrite (applyXminus (Xop X (Xsum fn (S n)) op opEq) (Xop X (Xsum fn n) op opEq)).
  destruct d; simpl.
  apply CRplus_morph. apply opEq.
  rewrite (applyXsum fn n x _ pF).
  rewrite (DomainProp _ x (pF (S n)) d1). reflexivity.
  apply CRopp_morph, opEq. rewrite (applyXsum fn n x _ pF).
  reflexivity.
Qed.

Lemma applyTelescopicOpInfSum
  : forall {R : ConstructiveReals} (X : Set)
      (fn : nat -> PartialFunction X)
      (op : CRcarrier R -> CRcarrier R)
      (opEq : forall x y : CRcarrier R, x == y -> op x == op y)
      (contract : forall x y : CRcarrier R,
          CRabs _ (op x - op y) <= CRabs _ (x - y))
      (x : X)
      (pF : forall n:nat, Domain (fn n) x)
      (pXT : forall n:nat, Domain (telescopicOp X fn op opEq n) x)
      (s : CRcarrier R),
    series_cv (fun n : nat => partialApply (fn n) x (pF n)) s
    -> series_cv
        (fun n : nat => partialApply (telescopicOp X fn op opEq n) x (pXT n))
        (op s).
Proof.
  intros. intros p. specialize (H p) as [N H0].
  exists N. intros n H. specialize (H0 n H).

  assert (forall (p:nat) (u : nat -> CRcarrier R),
             CRsum u (S p) == CRsum u p + u (S p)) as sum_shift.
  { intros. reflexivity. }
  assert (forall p0:nat,
             CRsum (fun k : nat => partialApply (telescopicOp X fn op opEq k) x (pXT k)) p0
             == op (CRsum (fun k : nat => partialApply (fn k) x (pF k)) p0)).
  { induction p0.
    - simpl. apply opEq. apply DomainProp.
    - rewrite sum_shift. rewrite IHp0.
      rewrite (applyTelescopicOp X fn op opEq p0 x pF).
      unfold CRminus. rewrite CRplus_comm, CRplus_assoc, CRplus_opp_l.
      rewrite CRplus_0_r. reflexivity. }
  rewrite H1.
  apply (CRle_trans
           _ (CRabs _ (CRsum (fun n : nat => partialApply (fn n) x (pF n)) n - s))).
  apply contract. assumption.
Qed.

Definition IabsOpContract {IS : IntegrationSpace}
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
           (fnL : forall n:nat, L (ElemFunc IS) (fn n))
           (op : CRcarrier (RealT (ElemFunc IS))
                 -> CRcarrier (RealT (ElemFunc IS)))
           (opEq : forall x y : CRcarrier (RealT (ElemFunc IS)),
               x == y -> op x == op y)
           (opL : forall f : PartialFunction (X (ElemFunc IS)),
               L (ElemFunc IS) f -> L (ElemFunc IS) (Xop (X (ElemFunc IS)) f op opEq))
           (contract : forall x y : CRcarrier (RealT (ElemFunc IS)),
               CRabs _ (op x - op y) <= CRabs _ (x - y))
           (zeroFix : op 0 == 0)
           (sumIAbsFn : CRcarrier (RealT (ElemFunc IS)))
  : series_cv (fun k : nat => Iabs (fn k) (fnL k)) sumIAbsFn
    -> { l : CRcarrier (RealT (ElemFunc IS))
            & series_cv (fun k => Iabs (telescopicOp _ fn op opEq k)
                                         (telescopicOpL fn fnL op opEq opL k)) l }.
Proof.
  intros.
  destruct (series_cv_maj (fun k => Iabs (telescopicOp _ fn op opEq k)
                                      (telescopicOpL fn fnL op opEq opL k))
                          (fun k => Iabs (fn k) (fnL k)) sumIAbsFn) as [sumOps cvOps].
  intro n. rewrite CRabs_right. apply INonDecreasing. intros.
  rewrite applyXabs. rewrite applyXabs. apply applyTelescopicOpMaj.
  assumption. assumption.
  apply (CRle_trans _ (CRabs _ (I IS (telescopicOp (X (ElemFunc IS)) fn op opEq n)
                                  (telescopicOpL fn fnL op opEq opL n)))).
  apply CRabs_pos. apply integralAbsMaj. assumption.
  exists sumOps. apply cvOps.
Qed.

Definition IntegralRepresentationOpContract
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (op : CRcarrier (RealT (ElemFunc IS))
                 -> CRcarrier (RealT (ElemFunc IS)))
           (opEq : forall x y : CRcarrier (RealT (ElemFunc IS)),
               x == y -> op x == op y)
           (opL : forall f : PartialFunction (X (ElemFunc IS)),
               L (ElemFunc IS) f -> L (ElemFunc IS) (Xop (X (ElemFunc IS)) f op opEq))
           (contract : forall x y : CRcarrier (RealT (ElemFunc IS)),
               CRabs _ (op x - op y) <= CRabs _ (x - y))
           (zeroFix : op 0 == 0)
  : IntegrableFunction f
    -> @IntegralRepresentation IS.
Proof.
  intros. destruct X.
  destruct (IabsOpContract _ _ op opEq opL contract zeroFix
                           (IntAbsSum x) (IntAbsSumCv x))
    as [sumOp cvOps].
  (* Weave the telescopic abs with the representation itself, to stay in
     the domain of f. *)
  exact (IntegralRepresentationWeave
           (Build_IntegralRepresentation
              IS
              (telescopicOp _ (IntFn x) op opEq)
              (telescopicOpL (IntFn x) (IntFnL x) op opEq opL)
              sumOp cvOps)
           (IntegralRepresentationWeave
              x (IntegralRepresentationScaleHalf f (-(1)) (existT _ x p)))).
Defined.

Definition IntegrableOpContract {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (op : CRcarrier (RealT (ElemFunc IS))
                 -> CRcarrier (RealT (ElemFunc IS)))
           (opEq : forall x y : CRcarrier (RealT (ElemFunc IS)),
               x == y -> op x == op y)
           (opL : forall f : PartialFunction (X (ElemFunc IS)),
               L (ElemFunc IS) f -> L (ElemFunc IS) (Xop (X (ElemFunc IS)) f op opEq))
           (contract : forall x y : CRcarrier (RealT (ElemFunc IS)),
               CRabs _ (op x - op y) <= CRabs _ (x - y))
           (zeroFix : op 0 == 0)
  : IntegrableFunction f
    -> IntegrableFunction (Xop (X (ElemFunc IS)) f op opEq).
Proof.
  intros.
  exists (IntegralRepresentationOpContract f op opEq opL contract zeroFix X).
  (* Prove partial restriction *)
  split.
  - (* Domain inclusion *)
    intros x xdf. simpl.
    unfold IntegralRepresentationOpContract in xdf;
    destruct X;
    destruct (IabsOpContract (IntFn x0) (IntFnL x0) op opEq opL contract zeroFix
                             (IntAbsSum x0) (IntAbsSumCv x0)).
    unfold IntegralRepresentationWeave, IntFn in xdf.
    pose proof (domainInfinSumWeaveR _ _ _ x xdf) as d0.
    pose proof (domainInfinSumWeaveL _ _ _ x d0) as pxDFn.
    destruct p. exact (d x pxDFn).
  - intros.
    unfold IntegralRepresentationOpContract, IntegralRepresentationWeave,
    IntFn, IntFnL, IntAbsSum, IntAbsSumCv in xD;
      unfold IntegralRepresentationOpContract, IntegralRepresentationWeave,
      IntFn, IntFnL, IntAbsSum, IntAbsSumCv ;
    destruct X as [[fn fnL sumIAbsFn H] [injF restr]];
    destruct (IabsOpContract _ _ op opEq opL contract zeroFix sumIAbsFn H)
      as [sumOp cvOps].
    pose proof (domainInfinSumWeaveL _ _ _ x xD) as pxDTn.
    pose proof (domainInfinSumWeaveR _ _ _ x xD) as x0.
    pose proof (domainInfinSumWeaveL _ _ _ x x0) as pxDFn.
    unfold IntFn in restr.
    apply applyInfiniteSumAbs.
    simpl (partialApply (Xop (X (ElemFunc IS)) f op opEq) x xG).
    apply (series_cv_eq
             (weaveSequences _
                (fun n : nat => partialApply (telescopicOp _ fn op opEq n) x
                                        (domainInfiniteSumAbsIncReverse _ x pxDTn n))
                (weaveSequences
                   _ (fun n : nat => partialApply (fn n) x
                                             (domainInfiniteSumAbsIncReverse _ x pxDFn n))
                   (fun n : nat => CRopp _ (partialApply (fn n) x
                                                 (domainInfiniteSumAbsIncReverse _ x pxDFn n)))))).
    + intro n.
      rewrite (partialApplyWeave
                    _ _ _ n x
                    (domainInfiniteSumAbsIncReverse _ x pxDTn (n/2))
                    (domainInfiniteSumAbsIncReverse _ x x0 (n/2))).
      unfold weaveSequences. destruct (Nat.even n). reflexivity.
      pose proof (partialApplyWeave _ fn (fun n => Xscale (-(1)) (fn n)) (n/2) x
                 (domainInfiniteSumAbsIncReverse fn x pxDFn (n / 2 / 2))
                 (domainInfiniteSumAbsIncReverse fn x pxDFn (n / 2 / 2))).
      rewrite H0.
      destruct (Nat.even (n/2)). reflexivity.
      rewrite applyXscale. rewrite <- CRopp_mult_distr_l.
      rewrite CRmult_1_l. reflexivity.
    + rewrite <- CRplus_0_r.
      rewrite <- (CRplus_opp_r (partialApply (XinfiniteSumAbs fn) x pxDFn)).
      apply weaveInfiniteSums.
      apply (applyTelescopicOpInfSum
               _ _ _ _ contract x (domainInfiniteSumAbsIncReverse _ x pxDFn)).
      apply applyInfiniteSumAbs. apply restr.
      apply weaveInfiniteSums.
      apply applyInfiniteSumAbs. reflexivity.
      apply series_cv_opp. apply applyInfiniteSumAbs. reflexivity.
Defined.

(* Like the Lebesgue integral, a function f is integrable
   when its absolute value is. *)
Definition IntegrableAbs {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction (Xabs f)
  := fun fInt => IntegrableOpContract
                f (CRabs _) (CRabs_morph_prop _)
                (LabsStable (ElemFunc IS))
                CRabs_triang_inv2
                (CRabs_right 0 (CRle_refl 0)) fInt.

(* The triangular inequality for integrals. *)
Lemma IntegralTriangle
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
    CRabs _ (Integral fInt)
    <= Integral (IntegrableAbs f fInt).
Proof.
  intros. apply CRabs_le. split.
  - rewrite <- IntegralOpp. apply IntegralNonDecreasing.
    intros x xdf xdg.
    rewrite applyXscale, applyXabs.
    rewrite (DomainProp f x xdf xdg).
    rewrite <- CRopp_mult_distr_l, CRmult_1_l.
    rewrite <- (CRopp_involutive (partialApply f x xdg)).
    apply CRopp_ge_le_contravar. rewrite CRopp_involutive.
    rewrite <- CRabs_opp. apply CRle_abs.
  - apply IntegralNonDecreasing. intros x xdf xdg.
    rewrite applyXabs.
    rewrite (DomainProp f x xdg xdf).
    apply CRle_abs.
Qed.


(* The integral of the absolute value of the function difference
   is a distance on the integrable functions. It is symmetric,
   satisfies the triangular inequality, but not exactly separated.
   When the integral distance between f and g is 0, then f and g
   are equal almost-everywhere, as defined in CMTFullSets. *)
Definition IntegralDistance {IS : IntegrationSpace}
           (f g : PartialFunction (X (ElemFunc IS)))
           (fInt : IntegrableFunction f)
           (gInt : IntegrableFunction g) : CRcarrier _
  := Integral (IntegrableAbs (Xminus f g) (IntegrableMinus _ _ fInt gInt)).

Lemma IntegralDistance_sym
  : forall { IS : IntegrationSpace }
      (f g : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (gInt : IntegrableFunction g),
    IntegralDistance f g fInt gInt == IntegralDistance g f gInt fInt.
Proof.
  intros. apply IntegralExtensional. intros.
  do 2 rewrite applyXabs.
  destruct xdf, xdg.
  rewrite (applyXminus f g), (applyXminus g f).
  rewrite CRabs_minus_sym. apply CRabs_morph, CRplus_morph.
  apply DomainProp. apply CRopp_morph. apply DomainProp.
Qed.

Definition Un_integral_cv { IS : IntegrationSpace }
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
           (f : PartialFunction (X (ElemFunc IS)))
           (fnInt : forall n:nat, IntegrableFunction (fn n))
           (fInt : IntegrableFunction f)
  := forall p : positive,
    { n : nat
    | forall i:nat, le n i -> IntegralDistance (fn n) f (fnInt n) fInt <= CR_of_Q _ (1#p) }.

Definition IntegrableMinOne {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction (XminConst f 1).
Proof.
  intros fInt. apply IntegrableOpContract.
  intros g gL. apply LminConstStable. exact (CRzero_lt_one _). exact gL.
  intros. apply CRmin_contract.
  apply CRmin_left. apply CRlt_asym, CRzero_lt_one. exact fInt.
Defined.

Definition FunctionRieszSpaceCompletion (IS : IntegrationSpace)
  : FunctionRieszSpace.
Proof.
  apply (Build_FunctionRieszSpace
           (X (ElemFunc IS)) (RealT (ElemFunc IS))
           IntegrableFunction).
  - intros f g H fInt. apply (IntegrableFunctionExtensional f g).
    destruct H. split. apply p. apply c. exact fInt.
  - exact IntegrablePlus.
  - exact IntegrableAbs.
  - intros. exact (IntegrableMinOne f X).
  - intros a f fInt. exact (IntegrableScale f a fInt).
Defined.

Definition IntegrableMinConst {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (a : CRcarrier _)
  : IntegrableFunction f
    -> 0 < a
    -> IntegrableFunction (XminConst f a)
  := fun fInt aPos => @LminConstStable (FunctionRieszSpaceCompletion IS)
                                    a f aPos fInt.

Definition IntegrableMaxConst {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (a : CRcarrier _)
  : IntegrableFunction f
    -> a < 0
    -> IntegrableFunction (XmaxConst f a).
Proof.
  intros fInt aPos. apply IntegrableOpContract.
  intros g gL. apply (Lext _ (Xscale (CRopp _ 1) (XminConst (Xscale (CRopp _ 1) g) ((CRopp _ 1)*a)))).
  split. split. intros x xdg. exact xdg.
  intros x xdg. exact xdg. intros. simpl.
  rewrite CRmin_max_mult_neg. do 2 rewrite <- CRopp_mult_distr_l.
  rewrite CRmult_1_l, CRmult_1_l, CRopp_involutive. apply CRmax_morph.
  apply DomainProp. reflexivity. apply (CRplus_le_reg_l 1).
  rewrite CRplus_opp_r, CRplus_0_r. apply CRlt_asym, CRzero_lt_one.
  apply LscaleStable. apply LminConstStable.
  rewrite <- CRopp_mult_distr_l, CRmult_1_l. apply (CRplus_lt_reg_l _ a).
  rewrite CRplus_opp_r, CRplus_0_r. exact aPos. apply LscaleStable, gL.
  intros. apply CRmax_contract.
  apply CRmax_left. apply CRlt_asym, aPos. exact fInt.
Defined.

Definition IntegrablePosPart {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction (XposPart f).
Proof.
  intros fInt.
  exact (IntegrableScale
              (Xplus f (Xabs f))
              (CR_of_Q _ (1#2))
              (IntegrablePlus f (Xabs f) fInt
                              (IntegrableAbs f fInt))).
Defined.

Definition IntegrableNegPart {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction (XnegPart f).
Proof.
  intros fInt.
  exact (IntegrableScale
              (Xminus (Xabs f) f)
              (CR_of_Q _ (1#2))
              (IntegrableMinus (Xabs f) f
                               (IntegrableAbs f fInt) fInt)).
Defined.

Definition IntegrableMinInt {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (n : nat)
  : IntegrableFunction f
    -> IntegrableFunction (XminConst f (INR n))
  := fun fInt => @LminIntStable (FunctionRieszSpaceCompletion IS)
                             n f fInt.

Definition IntegrableMin {IS : IntegrationSpace}
           (f g : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction g
    -> IntegrableFunction (Xmin f g).
Proof.
  intros fInt gInt.
  apply IntegrableMinus. assumption. apply IntegrableNegPart.
  apply IntegrableMinus; assumption.
Defined.

Definition IntegrableMax {IS : IntegrationSpace}
           (f g : PartialFunction (X (ElemFunc IS)))
  : IntegrableFunction f
    -> IntegrableFunction g
    -> IntegrableFunction (Xmax f g).
Proof.
  intros fInt gInt.
  apply IntegrablePlus. assumption. apply IntegrablePosPart.
  apply IntegrableMinus; assumption.
Defined.

Lemma intTelescopicAbs : forall {IS : IntegrationSpace}
                           (fn : nat -> PartialFunction (X (ElemFunc IS)))
                           (fnL : forall n:nat, L (ElemFunc IS) (fn n))
                           (n : nat),
    CRsum
      (fun n : nat =>
         I IS (telescopicOp (X (ElemFunc IS)) fn (CRabs _)
                            (CRabs_morph_prop _) n)
           (telescopicOpL fn fnL (CRabs _)
                          (CRabs_morph_prop _)
                          (fun f => LabsStable (ElemFunc IS) f) n)) n
    == Iabs (Xsum fn n) (LsumStable fn fnL n).
Proof.
  induction n.
  - reflexivity.
  - unfold CRsum. rewrite IHn. clear IHn.
    unfold telescopicOp, telescopicOpL, Xminus. rewrite Iadditive.
    rewrite Ihomogeneous.
    rewrite <- (CRopp_mult_distr_l 1), CRmult_1_l.
    unfold Iabs, Xabs. rewrite <- CRplus_assoc, CRplus_comm, <- CRplus_assoc.
    rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.

(* If function f is the limit of the series fn,
   then the integral of |f| is the limit of
   the integrals of the partial sums |f1 + ... + fn| *)
Lemma IntegralAbsLimit : forall {IS : IntegrationSpace}
                           (f : PartialFunction (X (ElemFunc IS)))
                           (fInt : IntegrableFunction f),
    CR_cv _
      (fun n : nat =>
         (Iabs _ (LsumStable (IntFn (let (i,_) := fInt in i))
                             (IntFnL (let (i,_) := fInt in i)) n)))
      (Integral (IntegrableAbs f fInt)).
Proof.
  intros IS. assert (CRabs (RealT (ElemFunc IS)) 0 == 0) as CReal_abs_R0.
  { rewrite CRabs_right. reflexivity. apply CRle_refl. }
  intros.
  unfold Integral, IntegrableAbs,
  IntegrableOpContract, IntegralRepresentationOpContract.
  destruct fInt as [x p],
                   (IabsOpContract (IntFn x) (IntFnL x) (CRabs _)
                                   (CRabs_morph_prop _)
            (LabsStable (ElemFunc IS)) CRabs_triang_inv2 (CRabs_right 0 (CRle_refl 0))
            (IntAbsSum x) (IntAbsSumCv x)).
  do 2 rewrite IntegralRepresentationWeaveSum.
  rewrite IntegralHomogeneousHalf, <- CRopp_mult_distr_r,
  CRmult_1_r, CRplus_opp_r, CRplus_0_r.
  destruct x as [fn fnL sumIAbsFn H]; unfold IntFn, IntFnL.
  apply (CR_cv_eq _ (CRsum (fun n : nat =>
                                 I IS (telescopicOp (X (ElemFunc IS)) fn (CRabs _)
                                                   (CRabs_morph_prop _) n)
            (telescopicOpL fn fnL (CRabs _) (CRabs_morph_prop _)
               (fun (g : PartialFunction (X (ElemFunc IS))) (gL : L (ElemFunc IS) g) =>
                LabsStable (ElemFunc IS) g gL) n)))).
  2: apply (IntegralCv {|
                         IntFn := telescopicOp (X (ElemFunc IS)) fn (CRabs _)
                                              (CRabs_morph_prop _);
       IntFnL := telescopicOpL fn fnL (CRabs _) (CRabs_morph_prop _)
                   (fun (g : PartialFunction (X (ElemFunc IS))) (gL : L (ElemFunc IS) g) =>
                    LabsStable (ElemFunc IS) g gL);
       IntAbsSum := x0;
       IntAbsSumCv := s |}).
  intro n. rewrite intTelescopicAbs. reflexivity.
Qed.

Definition IntegralRepresentationL {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fL : L (ElemFunc IS) f)
  : @IntegralRepresentation IS.
Proof.
  pose (fun n:nat => match n with
                     | O => f
                     | _ => Izero IS
                     end) as fn.
  assert (forall n:nat, L (ElemFunc IS) (fn n)) as fnL.
  { intro n. unfold fn. destruct n. exact fL.
    apply Izero_is_L. }
  apply (Build_IntegralRepresentation
           IS fn fnL (Iabs f fL)).
  apply (CR_cv_eq _ (fun _:nat => Iabs f fL)).
  2: apply CR_cv_const. intro n. destruct n.
  apply IExtensional. intros. apply DomainProp.
  rewrite <- CRplus_0_r, decomp_sum. apply CRplus_morph.
  apply IExtensional. intros. apply DomainProp.
  rewrite (CRsum_eq _ (fun _ => 0)).
  rewrite sum_eq_R0. reflexivity. intros _. reflexivity.
  intros. unfold fn, Iabs.
  rewrite (IExtensional _ (Izero IS) _ (Izero_is_L IS)).
  apply Izero_is_zero. intros.
  rewrite applyXabs, applyIzero, applyIzero, CRabs_right.
  reflexivity. apply CRle_refl. apply le_n_S, le_0_n.
Defined.

Definition IntegrableL {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fL : L (ElemFunc IS) f)
  : IntegrableFunction f.
Proof.
  exists (IntegralRepresentationL f fL).
  split.
  - intros x xd. destruct xd as [xn lim]. exact (xn O).
  - intros. apply applyInfiniteSumAbs.
    apply (CR_cv_eq _ (fun _:nat => partialApply f x xG)).
    2: apply CR_cv_const. intro n. destruct n. apply DomainProp.
    rewrite <- CRplus_0_r, decomp_sum. apply CRplus_morph.
    apply DomainProp. rewrite (CRsum_eq _ (fun _ => 0)).
    rewrite sum_eq_R0. reflexivity. intros _. reflexivity.
    intros. unfold IntegralRepresentationL, IntFn.
    apply applyIzero. apply le_n_S, le_0_n.
Defined.

Lemma IntegralLstable : forall {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (fL : L (ElemFunc IS) f),
    Integral (IntegrableL f fL) == I IS f fL.
Proof.
  intros. unfold IntegrableL.
  pose proof (IntegralCv (IntegralRepresentationL f fL)).
  apply (CR_cv_unique (fun n => I IS f fL)).
  2: apply CR_cv_const.
  apply (CR_cv_eq _ (CRsum (fun n : nat =>
         I IS (IntFn (IntegralRepresentationL f fL) n) (IntFnL (IntegralRepresentationL f fL) n)))).
  2: exact H. intro n. destruct n. reflexivity.
  symmetry.
  rewrite <- CRplus_0_r, decomp_sum. apply CRplus_morph.
  apply IExtensional. intros. apply DomainProp.
  rewrite (CRsum_eq _ (fun _ => 0)).
  rewrite sum_eq_R0. reflexivity. intros _. reflexivity.
  intros. simpl. apply Izero_is_zero.
  apply le_n_S, le_0_n.
Qed.

Fixpoint IntegrableSum {IS : IntegrationSpace}
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
           (fnInt : forall n:nat, IntegrableFunction (fn n))
           (n : nat)
  : IntegrableFunction (Xsum fn n).
Proof.
  destruct n.
  - apply fnInt.
  - simpl. apply IntegrablePlus. apply IntegrableSum. exact fnInt. apply fnInt.
Defined.

Definition IntegralRepresentationAbs { IS : IntegrationSpace }
  : @IntegralRepresentation IS -> @IntegralRepresentation IS.
Proof.
  intro fInt.
  pose (fun n:nat => Xabs (IntFn fInt n)) as fn.
  assert (forall n:nat, L (ElemFunc IS) (fn n)) as fnL.
  { intro n. unfold fn. apply (LabsStable (ElemFunc IS)), IntFnL. }
  apply (Build_IntegralRepresentation
           IS fn fnL (IntAbsSum fInt)).
  apply (series_cv_eq (fun n : nat => Iabs (IntFn fInt n) (IntFnL fInt n))).
  2: apply fInt. intro n. apply IExtensional.
  intros. unfold fn.
  rewrite (applyXabs (Xabs (IntFn fInt n))), CRabs_right.
  apply DomainProp. rewrite applyXabs. apply CRabs_pos.
Defined.

Lemma IntegralRepresentationAbsVal
  : forall {IS : IntegrationSpace}
      (fInt : @IntegralRepresentation IS),
    IntegralSeries (IntegralRepresentationAbs fInt) == IntAbsSum fInt.
Proof.
  intros.
  apply (CR_cv_unique (CRsum (fun n => Iabs (IntFn fInt n) (IntFnL fInt n)))).
  exact (IntegralCv (IntegralRepresentationAbs fInt)).
  apply fInt.
Qed.

Definition IntegrableSelf { IS : IntegrationSpace }
           (fInt : @IntegralRepresentation IS)
  : IntegrableFunction (XinfiniteSumAbs (IntFn fInt)).
Proof.
  exists fInt. apply PartialRestriction_refl.
Defined.
