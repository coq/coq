(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* A lemma to simplify the proofs of Icontinuous in integration spaces.
   It looks classical because it does not need to give a convergence modulus. *)

Require Import QArith.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructiveDiagonal.
Require Import ConstructivePartialFunctions.
Require Import CMTbase.
Require Import CMTIntegrableFunctions.

Local Open Scope ConstructiveReals.


Lemma Rmult_continuous_zero {R : ConstructiveReals} (x eps : CRcarrier R)
  : 0 < eps -> { alpha : CRcarrier R & prod (0 < alpha) (alpha * x < eps) }.
Proof.
  intros. destruct (CRltLinear R).
  destruct (s 0 x 1 (CRzero_lt_one R)).
  - assert (0 < x + 1).
    { apply (CRlt_trans _ (0 + 1)). rewrite CRplus_0_l.
      exact (CRzero_lt_one R). apply CRplus_lt_compat_r. exact c. }
    exists (eps * CRinv R (x+1) (inr H0)). split.
    apply CRmult_lt_0_compat. exact H. apply CRinv_0_lt_compat.
    exact H0.
    rewrite <- (CRmult_1_r eps). do 2 rewrite CRmult_assoc.
    apply CRmult_lt_compat_l. exact H.
    rewrite CRmult_1_l.
    apply (CRmult_lt_reg_l (x+1)). exact H0.
    rewrite <- CRmult_assoc, CRinv_r.
    rewrite CRmult_1_l, CRmult_1_r.
    rewrite <- (CRplus_0_r x), CRplus_assoc. apply CRplus_lt_compat_l.
    rewrite CRplus_0_l. exact (CRzero_lt_one R).
  - exists eps. split. exact H. rewrite <- (CRmult_1_r eps).
    rewrite CRmult_assoc. rewrite CRmult_1_l.
    exact (CRmult_lt_compat_l _ _ _ H c).
Qed.

(* Build an increasing sequence that respects sequence bound *)
Fixpoint ControlSubSeqCv {R : ConstructiveReals}
         (un : nat -> CRcarrier R) (l : CRcarrier R) (bound : nat -> CRcarrier R)
         (_ : CR_cv _ un l)
         (_ : forall k:nat, 0 < bound k)
         (n : nat) { struct n }
  : { p : nat & CRabs _ (un p - l) < bound n }.
Proof.
  destruct n.
  - intros.
    pose proof (Un_cv_nat_real _ l H (bound O) (H0 O)) as [p pmaj].
    exists p. apply pmaj, le_refl.
  - intros.
    pose proof (Un_cv_nat_real _ l H (bound (S n)) (H0 (S n))) as [p pmaj].
    exists (max p (S (let (k,_) := ControlSubSeqCv R un l bound H H0 n in k))).
    apply pmaj, Nat.le_max_l.
Defined.

Lemma ControlSubSeqCvInc
  : forall {R : ConstructiveReals}
      (un : nat -> CRcarrier R) (l : CRcarrier R) (bound : nat -> CRcarrier R)
      (cv : CR_cv _ un l)
      (boundPos : forall k:nat, 0 < bound k)
      (n : nat),
    lt (let (k,_) := ControlSubSeqCv un l bound cv boundPos n in k)
       (let (k,_) := ControlSubSeqCv un l bound cv boundPos (S n) in k).
Proof.
  intros. simpl.
  destruct (Un_cv_nat_real un l cv (bound (S n)) (boundPos (S n))),
  (ControlSubSeqCv un l bound cv boundPos n).
  apply (lt_le_trans _ (S x0)). apply le_n_S, le_refl.
  apply Nat.le_max_r.
Qed.

Definition PrependSeq {X : Type} (x : X) (un : nat -> X) (n : nat)
  := match n with
     | O => x
     | S p => un p
     end.

Lemma PrependSeqL : forall (E : FunctionRieszSpace)
                      (f : PartialFunction (X E))
                      (un : nat -> PartialFunction (X E)),
    L E f
    -> (forall n:nat, L E (un n))
    -> forall n:nat, L E (PrependSeq f un n).
Proof.
  intros E f un H H0 n. unfold PrependSeq. destruct n.
  exact H. apply H0.
Defined.

Lemma PrependSeqSeries
  : forall {R : ConstructiveReals} (x : CRcarrier R)
      (un : nat -> CRcarrier R) (l : CRcarrier R),
    series_cv un l
    -> series_cv (PrependSeq x un) (x + l).
Proof.
  intros. intros n. specialize (H n) as [p pmaj].
  exists (S p). intros.
  destruct i. exfalso; inversion H. apply le_S_n in H.
  rewrite decomp_sum. simpl.
  setoid_replace (x + CRsum (fun i0 : nat => un i0) i - (x + l))
    with (CRsum (fun i0 : nat => un i0) i - l).
  apply pmaj. exact H. 2: apply le_n_S, le_0_n.
  unfold CRminus. rewrite (CRplus_comm x).
  rewrite CRplus_assoc. apply CRplus_morph.
  reflexivity. rewrite CRopp_plus_distr, <- CRplus_assoc.
  rewrite CRplus_opp_r, CRplus_0_l. reflexivity.
Qed.

Lemma PosSumMaj : forall {R : ConstructiveReals} (un : nat -> CRcarrier R)
                    (a : CRcarrier R) (k : nat),
    (forall n:nat, 0 <= un n)
    -> CRsum un k <= a
    -> un k <= a.
Proof.
  destruct k.
  - intros. exact H0.
  - intros. simpl in H0. rewrite <- (CRplus_0_l (un (S k))).
    apply (CRle_trans _ (CRsum un k + un (S k))).
    apply CRplus_le_compat. apply cond_pos_sum. exact H.
    apply CRle_refl. exact H0.
Qed.

Lemma CRplus_eq_compat_l : forall {R : ConstructiveReals} (a b c : CRcarrier R),
    b == c
    -> a + b == a + c.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma pow2inv : forall {R : ConstructiveReals} (n p:nat),
    CRpow (CR_of_Q R 2) n * CRpow (CR_of_Q R (1 # 2)) (n + p)
    == CRpow (CR_of_Q R (1 # 2)) p.
Proof.
  induction p.
  - simpl. rewrite Nat.add_0_r, pow_mult.
    rewrite (pow_proper (CR_of_Q R 2 * CR_of_Q R (1 # 2)) 1).
    apply pow_one. rewrite <- CR_of_Q_mult.
    setoid_replace (2 * (1 # 2))%Q with 1%Q. apply CR_of_Q_one. reflexivity.
  - rewrite Nat.add_succ_r.
    transitivity (CRpow (CR_of_Q R 2) n * (CR_of_Q R (1 # 2) * CRpow (CR_of_Q R (1 # 2)) (n + p))).
    reflexivity. rewrite <- CRmult_assoc.
    rewrite (CRmult_comm (CRpow (CR_of_Q R 2) n)).
    rewrite CRmult_assoc, IHp. reflexivity.
Qed.

Lemma seq_cv_le : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (l a : CRcarrier R),
    CR_cv R un l
    -> (forall n:nat, un n <= a)
    -> l <= a.
Proof.
  intros. apply (CR_cv_bound_up un a l O).
  intros. apply H0. apply H.
Qed.

Lemma IcontinuousClassic
  : forall (E : FunctionRieszSpace)
      (I : forall f : PartialFunction (X E), (L E) f -> CRcarrier _)
      (Ihomogeneous : forall (a : CRcarrier _)
                        (f : PartialFunction (X E))
                        (fL : L E f),
          I (Xscale a f) (LscaleStable E a f fL)
          == a * (I f fL))
      (IadditiveIterate : forall (fn : nat -> PartialFunction (X E))
                            (fnL : forall n:nat, L E (fn n))
                            (N : nat),
          I (Xsum fn N) (LsumStable fn fnL N)
          == CRsum (fun n : nat => I (fn n) (fnL n)) N),
    (forall (f : PartialFunction (X E)) (fL : (L E) f),
        (* Usually the function Z is a plateau at 1 that contains
           the support of f. *)
        { ZL : { Z : PartialFunction (X E) & prod ((L E) Z) (nonNegFunc Z) }
               & forall (fn : nat -> PartialFunction (X E))
                   (fnL : forall n:nat, (L E) (fn n)),
              (forall n:nat, nonNegFunc (fn n))
              -> series_cv_lim_lt (fun n => I (fn n) (fnL n))
                                 (I f fL)
              -> { x : CommonPointFunSeq _ f fn
                 | (let (Z,_) := ZL in exists xz : Domain Z (cpx _ _ _ x),
                       partialApply Z (cpx _ _ _ x) xz == 1)
                   /\ forall k:nat, CRsum (fun n => partialApply (fn n) (cpx _ _ _ x) (cpxFn _ _ _ x n)) k
                            <= partialApply f (cpx _ _ _ x) (cpxF _ _ _ x) } })
    -> ElemIntegralContinuous I.
Proof.
  intros E I Ihomogeneous Iadd cont f fn fL fnL nonneg intMaj.
  specialize (cont f) as [[Z [ZL Zpos]] cont].
  destruct intMaj as [l [lcv lmaj]].
  destruct (Rmult_continuous_zero (I Z ZL + 1) (I f fL - l))
    as [alpha [alphapos alphamaj]].
  rewrite <- (CRplus_opp_r l).
  apply CRplus_lt_compat_r, lmaj.
  assert (forall k : nat, (0 < (fun k0 : nat => CRpow (CR_of_Q _ (1#2)) (2 * k0 + 2)%nat * alpha) k))
    as boundPos.
  { intro k. apply CRmult_lt_0_compat.
    apply pow_lt. exact Rlt_0_half. exact alphapos. }
  pose (PrependSeq O (fun i => S ( let (k,_) := ControlSubSeqCv
                   (CRsum (fun n : nat => I (fn n) (fnL n))) l
                   (fun k => (CRpow (CR_of_Q _ (1#2)) (2*k + 2) * alpha )) lcv boundPos i
                                in k))) as n.
  assert (forall k:nat, lt (n k) (n (S k))) as ninc.
  { intro k. unfold n, PrependSeq. destruct k.
    unfold ControlSubSeqCv.
    destruct (Un_cv_nat_real (CRsum (fun n0 : nat => I (fn n0) (fnL n0))) l lcv).
    apply le_n_S, le_0_n. apply le_n_S.
    apply (ControlSubSeqCvInc
             (CRsum (fun n0 : nat => I (fn n0) (fnL n0))) l
             (fun k0 : nat => CRpow (CR_of_Q _ (1#2)) (2 * k0 + 2) * alpha)). }
  (* Avoid the main mass of the series lcv, to focus on
     its convergence speed. Therefore seq starts at n 1. *)
  pose (PrependSeq (Xscale alpha Z)
                   (weaveSequences
                        _ fn (fun i => Xscale (CRpow (CR_of_Q _ 2) i) (Xsum (fun k => fn (n (S i) + k)%nat)
                                                          (pred (n (S (S i)) - n (S i)))))))
    as seq.
  pose (PrependSeqL E (Xscale alpha Z)
                    (weaveSequences
                        _ fn (fun i => Xscale (CRpow (CR_of_Q _ 2) i) (Xsum (fun k => fn (n (S i) + k)%nat)
                                                          (pred (n (S (S i)) - n (S i))))))
                    (LscaleStable E alpha Z ZL)
                    (weaveSequencesL E fn fnL _
                                     (fun n0 => LscaleStable E (CRpow (CR_of_Q _ 2) n0) _ (LsumStable _ (fun i => fnL _) _))))
    as seqL.
  assert (forall k:nat, nonNegFunc (seq k)) as seqPos.
  { intros k x xdf.
    unfold seq, PrependSeq in xdf; unfold seq, PrependSeq; destruct k.
    rewrite applyXscale. rewrite <- (CRmult_0_r alpha).
    apply CRmult_le_compat_l. apply CRlt_asym, alphapos.
    apply Zpos. unfold weaveSequences. unfold weaveSequences in xdf.
    destruct (Nat.even k). apply nonneg.
    rewrite applyXscale. rewrite <- (CRmult_0_r (CRpow (CR_of_Q _ 2) (k/2))).
    apply CRmult_le_compat_l.
    apply CRlt_asym, pow_lt. simpl.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    apply nonNegSumFunc. intros. apply nonneg. }
  destruct (cont seq seqL seqPos) as [x xgood].
  - destruct (series_cv_maj
                (fun i : nat => CRpow (CR_of_Q _ 2) i * (CRsum (fun k => I (fn (n (S i) + k)%nat)
                                                          (fnL (n (S i) + k)%nat))
                                           (pred (n (S (S i)) - n (S i)))))
                (fun i => CRpow (CR_of_Q _ (1#2)) (S i) * alpha)
                alpha).
    + intros. rewrite CRabs_mult. rewrite CRabs_right.
      destruct (n (S n0)) eqn:des.
      exfalso; pose proof (ninc n0); rewrite des in H; inversion H.
      pose proof (sum_assoc (fun k => I (fn k) (fnL k))
                            n1 (Init.Nat.pred (n (S (S n0)) - S n1))).
      apply (CRplus_eq_compat_l (-CRsum (fun k : nat => I (fn k) (fnL k)) n1)) in H.
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l in H.
      rewrite <- H. clear H.
      replace (S n1 + pred (n (S (S n0)) - S n1))%nat
        with (pred (n (S (S n0)))).
      setoid_replace  (- CRsum (fun k : nat => I (fn k) (fnL k)) n1 +
      CRsum (fun k : nat => I (fn k) (fnL k)) (pred (n (S (S n0)))))
        with (l - CRsum (fun k : nat => I (fn k) (fnL k)) n1 +
      (CRsum (fun k : nat => I (fn k) (fnL k)) (pred (n (S (S n0)))) - l)).
      apply (CRle_trans _ (CRpow (CR_of_Q _ 2) n0 *
                           (CRabs _ (l - CRsum (fun k : nat => I (fn k) (fnL k)) n1)
                            + CRabs _ (CRsum (fun k : nat => I (fn k) (fnL k))
                                                (pred (n (S (S n0)))) - l)))).
      apply CRmult_le_compat_l.
      apply CRlt_asym, pow_lt. simpl. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_lt. reflexivity.
      apply CRabs_triang. rewrite CRmult_plus_distr_l.
      apply (CRle_trans
               _ ((CRpow (CR_of_Q _ 2) n0) * CRpow (CR_of_Q _ (1#2)) (2 * n0 + 2) * alpha
                  + (CRpow (CR_of_Q _ 2) n0) * CRpow (CR_of_Q _ (1#2)) (2 * (S n0) + 2) * alpha)).
      apply CRplus_le_compat.
      rewrite CRmult_assoc. apply CRmult_le_compat_l.
      apply CRlt_asym, pow_lt. simpl. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_lt. reflexivity.
      replace n1 with (pred (n (S n0))). 2: rewrite des; reflexivity.
      unfold n, PrependSeq, proj1_sig, pred.
      destruct (ControlSubSeqCv (CRsum (fun n2 : nat => I (fn n2) (fnL n2))) l
                                (fun k : nat => CRpow (CR_of_Q _ (1#2)) (2 * k + 2) * alpha)
                                lcv boundPos n0).
      apply CRlt_asym. rewrite CRabs_minus_sym. exact c.
      rewrite CRmult_assoc. apply CRmult_le_compat_l.
      apply CRlt_asym, pow_lt. simpl. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_lt. reflexivity.
      unfold n, PrependSeq, proj1_sig, pred.
      destruct (ControlSubSeqCv (CRsum (fun n2 : nat => I (fn n2) (fnL n2))) l
             (fun k : nat => CRpow (CR_of_Q _ (1#2)) (2 * k + 2) * alpha)
             lcv boundPos (S n0)).
      apply CRlt_asym, c.
      rewrite <- CRmult_plus_distr_r. apply CRmult_le_compat_r.
      apply CRlt_asym, alphapos.
      replace (2 * n0 + 2)%nat with (n0 + (1 + S n0))%nat.
      rewrite pow2inv.
      replace (2 * S n0 + 2)%nat with (n0 + (3 + S n0))%nat.
      rewrite pow2inv.
      rewrite <- (CRmult_1_l (CRpow (CR_of_Q _ (1 # 2)) (S n0))).
      apply (CRle_trans
               _ (CR_of_Q _ (1 # 2) * CRpow (CR_of_Q _ (1 # 2)) (S n0)
                  + CR_of_Q _ (1 # 2) * (CR_of_Q _ (1 # 2) * (CR_of_Q _ (1 # 2) * CRpow (CR_of_Q _ (1 # 2)) (S n0))))).
      apply CRle_refl.
      do 2 rewrite <- CRmult_assoc.
      rewrite <- CRmult_plus_distr_r. apply CRmult_le_compat_r.
      apply CRlt_asym, pow_lt. simpl. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_lt. reflexivity.
      rewrite <- CR_of_Q_mult, <- CR_of_Q_mult, <- CR_of_Q_plus, <- CR_of_Q_one.
      apply CR_of_Q_le. discriminate.
      rewrite Nat.add_comm. simpl. apply f_equal.
      rewrite <- (Nat.add_comm (S (n0 + 0))). simpl. apply f_equal.
      rewrite Nat.add_0_r. rewrite <- (Nat.add_comm 2). reflexivity.
      simpl. rewrite <- Nat.add_assoc. apply f_equal2. reflexivity.
      rewrite Nat.add_0_r, Nat.add_comm. reflexivity.
      unfold CRminus. rewrite (CRplus_comm l), CRplus_assoc.
      apply CRplus_morph. reflexivity.
      rewrite CRplus_comm, CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      reflexivity. do 2 rewrite <- Nat.sub_1_r.
      rewrite Nat.add_sub_assoc.
      rewrite Nat.add_comm, Nat.sub_add. reflexivity.
      rewrite <- des. apply (le_trans _ (S (n (S n0)))).
      apply le_S, le_refl. exact (ninc (S n0)).
      rewrite <- des. apply Nat.le_add_le_sub_r. apply ninc.
      apply CRlt_asym, pow_lt. simpl.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    + apply (CR_cv_proper _ (1*alpha)).
      apply series_cv_scale.
      apply (series_cv_eq (fun n0 : nat => CRpow (CR_of_Q _ (1 # 2)) n0 * CR_of_Q _ (1#2))).
      intros. apply CRmult_comm.
      apply (CR_cv_proper _ (CR_of_Q _ 2 * CR_of_Q _ (1#2))).
      apply series_cv_scale, GeoHalfTwo.
      rewrite <- CR_of_Q_mult. setoid_replace (2 * (1 # 2))%Q with 1%Q.
      apply CR_of_Q_one. reflexivity. apply CRmult_1_l.
    + clear cont. exists (alpha * I Z ZL + (l + x)). destruct p. split.
      apply (series_cv_eq
               (PrependSeq (alpha * (I Z ZL))
                           (weaveSequences (CRcarrier _) (fun k => I (fn k) (fnL k))
                                           (fun i => CRpow (CR_of_Q _ 2) i * (CRsum (fun k => I (fn (n (S i) + k)%nat) (fnL (n (S i) + k)%nat))
                                           (pred (n (S (S i)) - n (S i)))))))).
      intros. unfold seq, PrependSeq. destruct n0.
      simpl. rewrite Ihomogeneous. reflexivity.
      unfold seqL, weaveSequences, weaveSequencesL, PrependSeqL.
      clear seqL seqPos seq.
      destruct (Nat.even n0). reflexivity.
      rewrite Ihomogeneous, Iadd. reflexivity.
      apply PrependSeqSeries.
      apply weaveInfiniteSums. exact lcv. exact s.
      apply (CRplus_lt_reg_l _ (-l)).
      rewrite (CRplus_comm (alpha*I Z ZL)), <- CRplus_assoc, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l.
      apply (CRle_lt_trans _ (alpha * I Z ZL + alpha)).
      rewrite CRplus_comm.
      apply CRplus_le_compat_l. exact c.
      rewrite CRmult_plus_distr_l, CRmult_1_r in alphamaj.
      rewrite (CRplus_comm (-l)). exact alphamaj.
  - destruct x as [x xf xseqn].
    assert (forall n : nat, Domain (fn n) x) as xfn.
    { intro k.
      exact (domainWeaveEvenInc _ _ _ k x (xseqn (S (k * 2)))). }
    exists (Build_CommonPointFunSeq _ (X E) f fn x xf xfn).
    unfold cpx, cpxFn, cpxF.
    unfold cpx, cpxF, cpxFn in xgood. destruct xgood.
    (* Get the initial mass back *)
    destruct (series_cv_maj
                (fun i : nat => CRsum (fun k : nat => partialApply (fn (k + n i)%nat) x (xfn (k + n i)%nat))
                                    (n (S i) - n i - 1))
                (PrependSeq (CRsum (fun k:nat => partialApply (fn (k + n 0)%nat) x (xfn (k + n 0)%nat)) (n 1 - 1)%nat)
                            (fun j => CRpow (CR_of_Q _ (1#2)) j * (partialApply f x xf)))
                (CRsum (fun k:nat => partialApply (fn (k + n 0)%nat) x (xfn (k + n 0)%nat)) (n 1 - 1)%nat
                 + CR_of_Q _ 2 * partialApply f x xf)).
    + clear seqL. intros.
      rewrite CRabs_right.
      2: apply cond_pos_sum; intros; apply nonneg. unfold PrependSeq.
      destruct n0. apply CRle_refl.
      apply (PosSumMaj _ (partialApply f x xf) (S (S (2*n0)))) in H0.
      2: intros; apply seqPos.
      unfold pred, seq, PrependSeq in H0.
      rewrite Nat.mul_comm in H0.
      rewrite <- (partialApplyWeaveOdd
                    (X E) fn _ _ x
                    (domainWeaveOddInc (X E) fn _ n0 x (xseqn (S (S (n0 * 2)))))) in H0.
      rewrite applyXscale in H0.
      rewrite (applyXsum _ _ _ _ (fun k => xfn (n (S n0) + k)%nat)) in H0.
      intro abs. rewrite <- (Nat.add_0_r n0) in abs.
      apply (CRmult_lt_compat_l (CRpow (CR_of_Q _ 2) n0)) in abs.
      rewrite <- CRmult_assoc, pow2inv in abs. apply H0.
      apply (CRle_lt_trans _ (CRpow (CR_of_Q _ (1 # 2)) 0 * partialApply f x xf)).
      unfold CRpow. rewrite CRmult_1_l. apply CRle_refl.
      apply (CRlt_le_trans _ _ _ abs). apply CRmult_le_compat_l.
      apply CRlt_asym, pow_lt. simpl. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_lt; reflexivity.
      rewrite <- Nat.sub_1_r. rewrite Nat.add_0_r. apply sum_Rle. intros.
      rewrite Nat.add_comm. apply CRle_refl.
      apply pow_lt. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    + apply PrependSeqSeries, series_cv_scale, GeoHalfTwo.
    + clear seqL. destruct p as [i _].
      pose proof (infinite_sum_assoc
                    _ n x0 ninc
                    (fun k => nonneg k x (xfn k)) (eq_refl _) i).
      exists x0. split. exact H1.
      apply (CRle_lt_trans _ (partialApply f x xf - alpha)).
      apply (CRplus_le_reg_l alpha).
      rewrite <- (CRplus_comm (partialApply f x xf - alpha)).
      unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply (seq_cv_le (CRsum (PrependSeq alpha (fun k => partialApply (fn k) x (xfn k))))).
      apply PrependSeqSeries. exact H1.
      intros.
      specialize (H0 (2*n0)%nat).
      apply (CRle_trans
               _ (CRsum (fun n : nat => partialApply (seq n) x (xseqn n)) (2 * n0))).
      2: exact H0.
      destruct n0. unfold CRsum. simpl.
      destruct H. rewrite (DomainProp Z x _ x1), H, CRmult_1_r.
      apply CRle_refl. rewrite decomp_sum.
      rewrite (decomp_sum (fun n1 : nat => partialApply (seq n1) x (xseqn n1))).
      unfold seq, PrependSeq.
      apply CRplus_le_compat.
      destruct H. rewrite applyXscale, (DomainProp Z x _ x1), H, CRmult_1_r.
      apply CRle_refl. simpl (pred (S n0)).
      replace (pred (2 * S n0)) with (S (2*n0)).
      2: simpl; rewrite Nat.add_succ_r; reflexivity.
      rewrite (CRsum_eq _ (weaveSequences
                         (CRcarrier _) (fun i => partialApply (fn i) x (xfn i))
                         (fun i => CRpow (CR_of_Q _ 2) i * (CRsum (fun k => partialApply (fn (n (S i) + k)%nat) x (xfn (n (S i) + k)%nat))
                                                         (pred (n (S (S i)) - n (S i))) )))
                      (S (2 * n0))).
      rewrite weaveSequencesSum.
      rewrite <- (CRplus_0_r
                   (CRsum (fun i0 : nat => partialApply (fn i0) x (xfn i0)) n0)).
      apply CRplus_le_compat.
      rewrite <- (Nat.mul_comm n0). pose proof (Nat.div_add 1 n0 2).
      simpl in H2. simpl. rewrite H2. apply CRle_refl. auto.
      apply cond_pos_sum. intros.
      rewrite <- (CRmult_0_r (CRpow (CR_of_Q _ 2) k)). apply CRmult_le_compat_l.
      apply CRlt_asym, pow_lt. simpl. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_lt; reflexivity. apply cond_pos_sum.
      intros. apply nonneg.
      intros.
      rewrite (partialApplyWeave (X E) fn _ i0 x (xfn (i0/2)%nat)
                                 (domainWeaveOddInc (X E) fn _ (i0/2) x (xseqn (S (S ((i0/2) * 2)))))
                                 (xseqn (S i0))).
      unfold weaveSequences. destruct (Nat.even i0). reflexivity.
      rewrite applyXscale. apply CRmult_morph. reflexivity.
      apply applyXsum. apply le_n_S, le_0_n.
      apply le_n_S, le_0_n.
      rewrite <- (CRplus_0_r (partialApply f x xf)).
      unfold CRminus. rewrite CRplus_assoc. apply CRplus_lt_compat_l.
      apply (CRplus_lt_reg_l _ alpha).
      rewrite CRplus_0_l, CRplus_opp_r, CRplus_0_r. exact alphapos.
Qed.
