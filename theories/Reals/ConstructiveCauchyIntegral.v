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
  The Cauchy integral of uniformly continuous functions R -> R.
  It is the simplest integration theory, and the one used in
  the proof of the Picard-Lindelhöf theorem.

  The Cauchy integral approximates uniformly continuous functions
  by histograms, which widths tend to 0. In other words,
  it is the proof that sequences of rectangles integrate continuous
  functions.
 *)

Require Import List Permutation Orders Sorted Mergesort.
Require Import QArith Qpower.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructiveRcomplete.
Require Import ConstructiveDiagonal.
Require Import ConstructiveUniformCont.

Local Open Scope ConstructiveReals.


(* Elementary theory of integration for the uniformly continuous
   functions. To integrate discontinuous functions, the full
   constructive measure theory will be developped later. *)

Record IntervalPartition {R : ConstructiveReals} {a b : CRcarrier R} : Set :=
  {
    ipt_seq : nat -> CRcarrier R;
    ipt_last : nat;
    ipt_head : a == ipt_seq 0;
    ipt_lastB : b == ipt_seq (S ipt_last);
    ipt_ordered : forall n:nat, le n ipt_last -> ipt_seq n <= ipt_seq (S n);
  }.

Lemma ipt_ordered_transit : forall {R : ConstructiveReals} (a b : CRcarrier R)
                              (P : @IntervalPartition R a b) (n p : nat),
   le n p -> le p (S (ipt_last P)) -> ipt_seq P n <= ipt_seq P p.
Proof.
  induction p.
  - intros. inversion H. apply CRle_refl.
  - intros. apply Nat.le_succ_r in H. destruct H.
    + apply (CRle_trans _ (ipt_seq P p)). apply (IHp H).
      apply (le_trans _ (ipt_last P)). apply le_S_n. exact H0.
      apply le_S, le_refl. apply P. apply le_S_n. exact H0.
    + subst n. apply CRle_refl.
Qed.

Fixpoint PartitionMesh {R : ConstructiveReals}
         (points : nat -> CRcarrier R) (len : nat) : CRcarrier R
  := match len with
     | O => 0
     | S l => CRmax (points len - points l) (PartitionMesh points l)
     end.

Lemma PartitionMesh_ext : forall {R : ConstructiveReals}
                            (un vn : nat -> CRcarrier R) (len : nat),
    (forall n:nat, le n len -> un n == vn n)
    -> PartitionMesh un len == PartitionMesh vn len.
Proof.
  induction len.
  - intros. reflexivity.
  - intros. simpl.
    rewrite IHlen. rewrite (H (S len)), (H len). reflexivity.
    apply le_S, le_refl. apply le_refl.
    intros. apply H. apply le_S, H0.
Qed.

Lemma PartitionMesh_nonneg
  : forall {R : ConstructiveReals} (xn : nat -> CRcarrier R) (n : nat),
    0 <= PartitionMesh xn n.
Proof.
  induction n. apply CRle_refl. simpl.
  apply (CRle_trans _ _ _ IHn), CRmax_r.
Qed.

Lemma AllIntervalsSmallerThanMesh
  : forall {R : ConstructiveReals} (a b : CRcarrier R)
      (P : @IntervalPartition R a b) (n : nat),
    le n (ipt_last P)
    -> ipt_seq P (S n) - ipt_seq P n
      <= PartitionMesh (ipt_seq P) (S (ipt_last P)).
Proof.
  intros. destruct P; unfold ipt_seq, ipt_last; simpl in H.
  clear ipt_lastB0 b.
  generalize dependent ipt_last0. induction ipt_last0.
  - intros. inversion H. apply CRmax_l.
  - intros.
    assert (forall n : nat, le n ipt_last0 -> (ipt_seq0 n <= ipt_seq0 (S n))).
    { intros. apply ipt_ordered0. apply (le_trans _ ipt_last0 _ H0).
      apply le_S, le_refl. }
    specialize (IHipt_last0 H0). apply Nat.le_succ_r in H.
    destruct H.
    + specialize (IHipt_last0 H).
      apply (CRle_trans _ _ _ IHipt_last0). apply CRmax_r.
    + rewrite <- H. apply CRmax_l.
Qed.

Definition IntegralFiniteSum {R : ConstructiveReals}
           (f : CRcarrier R -> CRcarrier R)
           (x partition : nat -> CRcarrier R) (last : nat) : CRcarrier R
  := CRsum (fun n:nat => f (x n) * (partition (S n) - partition n)) last.

Definition WeavedLists {R : ConstructiveReals}
           (x partition : nat -> CRcarrier R) (last : nat) : Prop
  := forall n:nat, le n last -> (partition n <= x n /\ x n <= partition (S n)).

Definition IntervalPartitionRefinement {R : ConstructiveReals}
           (a b : CRcarrier R)
           (small big : @IntervalPartition R a b) (subseq : nat -> nat) : Prop
  := (forall n:nat, le n (S (ipt_last small))
             -> ipt_seq big (subseq n) == ipt_seq small n)
     /\ (forall n p:nat, n < p -> p <= S (ipt_last small) -> subseq n < subseq p)%nat
     /\ (forall n:nat, n <= S (ipt_last small) -> subseq n <= S (ipt_last big))%nat.

Lemma in_refinement_packet
  : forall {R : ConstructiveReals} (a b : CRcarrier R) (n i : nat)
      (x y : nat -> CRcarrier R)
      (P Q : @IntervalPartition R a b)
      (subseq : nat -> nat),
    WeavedLists x (ipt_seq P) (ipt_last P)
    -> WeavedLists y (ipt_seq Q) (ipt_last Q)
    -> IntervalPartitionRefinement _ _ P Q subseq
    -> le n (ipt_last P)
    -> le (subseq n) i
    -> lt i (subseq (S n)) (* i = S n can overflow in the last packet *)
    -> CRabs _ (x n - y i)
      <= PartitionMesh (ipt_seq P) (S (ipt_last P)).
Proof.
  intros.
  assert (ipt_seq P n <= y i /\ y i <= ipt_seq P (S n)).
  { specialize (H0 i). split.
    apply (CRle_trans _ (ipt_seq Q i)).
    apply (CRle_trans _ (ipt_seq Q (subseq n))).
    destruct H1. rewrite H1. apply CRle_refl.
    apply (le_trans _ _ _ H2). apply le_S, le_refl.
    apply ipt_ordered_transit. exact H3.
    destruct H1. apply (le_trans _ (subseq (S n))).
    apply (le_trans _ (S i)). apply le_S, le_refl. exact H4.
    apply H5. apply le_n_S. exact H2.
    apply H0. destruct H1.
    apply le_S_n. apply (le_trans _ _ _ H4).
    apply H5, le_n_S, H2.
    apply (CRle_trans _ (ipt_seq Q (S i))). apply H0.
    apply le_S_n. apply (le_trans _ _ _ H4). destruct H1.
    apply H5, le_n_S, H2.
    destruct H1.
    apply (CRle_trans _ (ipt_seq Q (subseq (S n)))).
    apply ipt_ordered_transit. exact H4.
    apply H5, le_n_S, H2.
    rewrite H1. apply CRle_refl. apply le_n_S, H2.
  }
  apply (CRle_trans _ (ipt_seq P (S n) - ipt_seq P n)).
  apply Rsmaller_interval. apply H5. apply H5.
  apply H. exact H2. apply H. exact H2.
  apply AllIntervalsSmallerThanMesh. exact H2.
Qed.

Lemma partition_before_start
  : forall {R : ConstructiveReals} (a b : CRcarrier R)
      (P : @IntervalPartition R a b) (n : nat),
    le n (S (ipt_last P))
    -> ipt_seq P n == a -> (forall p:nat, le p n -> ipt_seq P p == a).
Proof.
  intros. pose proof (ipt_ordered_transit a b P).
  destruct P; unfold ipt_seq; simpl in H,H0,H2. split.
  - fold (a <= ipt_seq0 p). rewrite ipt_head0. apply H2. apply le_0_n.
    apply (le_trans _ _ _ H1). exact H.
  - intro abs. rewrite <- H0 in abs. apply (H2 p n).
    exact H1. exact H. exact abs.
Qed.

Lemma partition_after_end
  : forall {R : ConstructiveReals} (a b : CRcarrier R)
      (P : @IntervalPartition R a b) (n : nat),
    ipt_seq P n == b
    -> (forall p:nat, le n p -> le p (S (ipt_last P)) -> ipt_seq P p == b).
Proof.
  intros. pose proof (ipt_ordered_transit a b P).
  destruct P; unfold ipt_seq; simpl in H,H1,H2. split.
  - fold (b <= ipt_seq0 p). rewrite <- H. apply H2. exact H0. exact H1.
  - fold (ipt_seq0 p <= b).
    rewrite ipt_lastB0. apply H2. exact H1. apply le_refl.
Qed.

(* Sum on the refined partition, either grouped or not. *)
Lemma partition_sum_by_packets
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (a b : CRcarrier R)
      (y : nat -> CRcarrier R)
      (P Q : @IntervalPartition R a b)
      (subseq : nat -> nat),
    IntervalPartitionRefinement _ _ P Q subseq
    -> CRsum
        (fun n : nat =>
           CRsum
             (fun i : nat =>
                (f (y (i + subseq n)%nat) *
                 (ipt_seq Q (S i + subseq n) - ipt_seq Q (i + subseq n))))
             (pred (subseq (S n) - subseq n))) (ipt_last P)
      == CRsum (fun n : nat => (f (y n) * (ipt_seq Q (S n) - ipt_seq Q n)))
                  (ipt_last Q).
Proof.
  intros. destruct H, H0.
  (* Get rid of the last points equal to b *)
  transitivity (CRsum (fun n : nat => (f (y n) * (ipt_seq Q (S n) - ipt_seq Q n)))
                         (pred (subseq (S (ipt_last P))))).
  (* Get rid of the first points equal to a *)
  pose (fun n:nat => match n with O => O | S p => subseq n end) as shiftSubseq.
  transitivity ( CRsum
    (fun n0 : nat =>
     CRsum
       (fun i : nat =>
        (f (y (i + shiftSubseq n0)%nat) *
         (ipt_seq Q (S i + shiftSubseq n0) - ipt_seq Q (i + shiftSubseq n0))))
       (pred (shiftSubseq (S n0) - shiftSubseq n0))) (ipt_last P)).
  - apply CRsum_eq. intros. destruct i.
    2: apply CRsum_eq; reflexivity. unfold shiftSubseq.
    destruct (Nat.le_exists_sub (S (subseq O)) (subseq 1%nat)) as [p [peq _]].
    apply H0. auto. apply le_n_S, le_0_n.
    rewrite Nat.sub_0_r. rewrite peq.
    rewrite Nat.add_succ_r.
    replace (S (p + subseq 0%nat) - subseq 0)%nat with (S p).
    simpl. destruct (subseq O) eqn:des. rewrite Nat.add_0_r.
    apply CRsum_eq; reflexivity. rewrite <- (Nat.add_comm (S n)).
    rewrite sum_assoc. symmetry.
    rewrite <- (CRplus_0_l
                 (CRsum
    (fun i : nat =>
     f (y (i + S n)%nat) * (ipt_seq Q (S (i + S n)) - ipt_seq Q (i + S n))) p)).
    apply CRplus_morph.
    rewrite (CRsum_eq _ (fun _ => 0 * 0)).
    rewrite sum_scale, CRmult_0_r. reflexivity.
    intros. rewrite CRmult_0_l. rewrite Nat.add_0_r.
    setoid_replace (ipt_seq Q (S i)) with a. setoid_replace (ipt_seq Q i) with a.
    unfold CRminus. rewrite CRplus_opp_r, CRmult_0_r.
    reflexivity. symmetry. rewrite (partition_before_start _ _ _ (subseq O)).
    reflexivity.
    apply H1, le_0_n. rewrite H. symmetry. apply P.
    apply le_0_n. rewrite des. apply (le_trans _ _ _ H3).
    apply le_S, le_refl.
    rewrite (partition_before_start _ _ _ (subseq O)). reflexivity.
    apply H1, le_0_n. rewrite H. symmetry. apply P.
    apply le_0_n. rewrite des. apply le_n_S. exact H3.
    apply CRsum_eq. intros. rewrite Nat.add_0_r, Nat.add_comm. reflexivity.
    rewrite Nat.sub_succ_l. apply f_equal.
    rewrite Nat.add_sub. reflexivity.
    rewrite <- (Nat.add_0_l (subseq O)). rewrite Nat.add_assoc.
    apply Nat.add_le_mono_r. apply le_0_n.
  - replace (pred (subseq (S (ipt_last P))))
      with (pred (shiftSubseq (S (ipt_last P)))).
    apply (sum_by_packets (fun n : nat => (f (y n) * (ipt_seq Q (S n) - ipt_seq Q n)))).
    intros. unfold shiftSubseq. destruct k. apply (le_lt_trans _ (subseq O)).
    apply le_0_n. apply H0. auto. apply le_n_S. exact H2.
    apply H0. apply le_refl. apply le_n_S. exact H2. reflexivity.
    reflexivity.
  - destruct (Nat.le_exists_sub (subseq (S (ipt_last P)))
                                (S (ipt_last Q))) as [p [peq _]].
    apply H1. apply le_refl.
    destruct p.
    replace (Init.Nat.pred (subseq (S (ipt_last P))))
      with (ipt_last Q). reflexivity.
    simpl in peq.
    rewrite <- peq. reflexivity.
    inversion peq. clear peq.
    assert (subseq (S (ipt_last P)) <> 0%nat).
    { intro abs. specialize (H0 (ipt_last P) (S (ipt_last P))
                                (le_refl _) (le_refl _)).
      rewrite abs in H0. inversion H0. }
    pose proof (Nat.succ_pred (subseq (S (ipt_last P))) H2).
    replace (ipt_last Q) with
        (S (pred (subseq (S (ipt_last P)))) + p)%nat.
    rewrite sum_assoc. symmetry.
    rewrite <- (CRplus_0_r
                 (CRsum (fun n : nat => f (y n) * (ipt_seq Q (S n) - ipt_seq Q n))
    (Init.Nat.pred (subseq (S (ipt_last P)))))).
    apply CRplus_morph. rewrite CRplus_0_r. reflexivity.
    rewrite (CRsum_eq _ (fun _ => 0 * 0)).
    rewrite sum_scale, CRmult_0_r. reflexivity.
    intros. rewrite CRmult_0_l. rewrite H4.
    setoid_replace (ipt_seq Q (S (subseq (S (ipt_last P)) + i))) with b.
    setoid_replace (ipt_seq Q (subseq (S (ipt_last P)) + i)) with b.
    unfold CRminus. rewrite CRplus_opp_r, CRmult_0_r.
    reflexivity.
    rewrite (partition_after_end _ _ _ (subseq (S (ipt_last P)))).
    reflexivity. rewrite H. symmetry. apply P. apply le_refl.
    rewrite <- (Nat.add_0_r (subseq (S (ipt_last P)))).
    rewrite <- Nat.add_assoc. apply Nat.add_le_mono_l, le_0_n.
    apply (le_trans _ (subseq (S (ipt_last P)) + p)).
    apply Nat.add_le_mono_l. exact H5. rewrite Nat.add_comm, H3.
    apply le_S, le_refl.
    rewrite (partition_after_end _ _ _ (subseq (S (ipt_last P)))).
    reflexivity. rewrite H. symmetry. apply P. apply le_refl.
    apply (le_trans _ (S (subseq (S (ipt_last P))))).
    apply le_S, le_refl. apply le_n_S.
    rewrite <- (Nat.add_0_r (subseq (S (ipt_last P)))).
    rewrite <- Nat.add_assoc. apply Nat.add_le_mono_l, le_0_n.
    apply le_n_S. apply (le_trans _ (subseq (S (ipt_last P)) + p)).
    apply Nat.add_le_mono_l. exact H5. rewrite Nat.add_comm, H3.
    apply le_refl. rewrite H4, H3. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma UC_refine_integral
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (a b eps : CRcarrier R)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (x y : nat -> CRcarrier R)
      (P Q : @IntervalPartition R a b) (epsPos : 0 < eps)
      (subseq : nat -> nat),
    UniformCont f cont_mod
    -> WeavedLists x (ipt_seq P) (ipt_last P)
    -> WeavedLists y (ipt_seq Q) (ipt_last Q)
    -> IntervalPartitionRefinement _ _ P Q subseq
    -> (PartitionMesh (ipt_seq P) (S (ipt_last P))) < (cont_mod eps epsPos)
    -> CRabs _ (IntegralFiniteSum f x (ipt_seq P) (ipt_last P)
                 - IntegralFiniteSum f y (ipt_seq Q) (ipt_last Q))
      <= eps * (b-a).
Proof.
  (* Use subseq to make packets of summations *)
  intros.
  setoid_replace (IntegralFiniteSum f x (ipt_seq P) (ipt_last P)
           - IntegralFiniteSum f y (ipt_seq Q) (ipt_last Q))
    with (CRsum (fun n:nat => f (x n) *
                                  (CRsum (fun i => ipt_seq Q (S i + subseq n)
                                                   - ipt_seq Q (i + subseq n))
                                            (pred (subseq (S n) - subseq n))))
                   (ipt_last P)
          - (CRsum (fun n:nat => CRsum (fun i => f (y (i + subseq n)%nat) *
                                                     (ipt_seq Q (S i + subseq n)
                                                      - ipt_seq Q (i + subseq n)))
                                        (pred (subseq (S n) - subseq n)))
                      (ipt_last P))).
  - rewrite <- Rsum_minus.
    apply (CRle_trans _ _ _ (multiTriangleIneg _ _)).
    apply (CRle_trans _ (CRsum (fun k => eps * (ipt_seq P (S k) - ipt_seq P k))
                                  (ipt_last P))).
    + apply sum_Rle. intros n H4.
      rewrite CRmult_comm, <- sum_scale, <- Rsum_minus.
      apply (CRle_trans _ _ _ (multiTriangleIneg _ _)).
      apply (CRle_trans
               _ (CRsum
                    (fun k : nat =>
                       CRabs _ (f (x n) - f (y (plus k (subseq n))))
                       * (ipt_seq Q (S k + subseq n) - ipt_seq Q (k + subseq n)))
                    (pred (subseq (S n) - subseq n)))).
      apply sum_Rle. intros. rewrite <- (CRmult_comm (f (x n))).
      unfold CRminus. rewrite CRopp_mult_distr_l.
      rewrite <- CRmult_plus_distr_r, CRabs_mult. apply CRmult_le_compat_l.
      apply CRabs_pos. rewrite CRabs_right. apply CRle_refl.
      rewrite <- (CRplus_opp_r (ipt_seq Q (k + subseq n))).
      apply CRplus_le_compat. 2: apply CRle_refl.
      apply ipt_ordered.
      apply le_S_n. apply le_n_S in H5.
      apply (le_trans _ (subseq (S n))).
      rewrite Nat.succ_pred in H5.
      rewrite Nat.add_comm. apply Nat.lt_add_lt_sub_l. exact H5.
      intro abs.
      destruct H2, H6. specialize (H6 n (S n) (le_refl _)).
      apply Nat.sub_0_le in abs. apply (le_not_lt _ _ abs).
      apply H6, le_n_S, H4. apply H2. apply le_n_S, H4.
      apply (CRle_trans
               _ (CRsum
                    (fun k : nat =>
                       (ipt_seq Q (S k + subseq n) - ipt_seq Q (k + subseq n))
                       * eps)
                    (Init.Nat.pred (subseq (S n) - subseq n)))).
      apply sum_Rle. intros n0 H5. rewrite CRmult_comm.
      apply CRmult_le_compat_l.
      rewrite <- (CRplus_opp_r (ipt_seq Q (n0 + subseq n))).
      apply CRplus_le_compat. 2: apply CRle_refl.
      apply (ipt_ordered Q).
      apply le_n_S in H5. rewrite Nat.succ_pred in H5.
      apply le_S_n.
      apply (le_trans _ (subseq (S n))).
      rewrite Nat.add_comm. apply Nat.lt_add_lt_sub_l. exact H5.
      apply H2, le_n_S, H4.
      intro abs.
      destruct H2, H6. specialize (H6 n (S n) (le_refl _)).
      apply Nat.sub_0_le in abs. apply (le_not_lt _ _ abs).
      apply H6, le_n_S, H4.
      destruct H. apply CRlt_asym. apply (c0 eps _ _ epsPos).
      apply (CRle_lt_trans _ (PartitionMesh (ipt_seq P) (S (ipt_last P)))).
      2: exact H3.
      apply (in_refinement_packet a b n (n0 + subseq n) x y P Q subseq H0 H1 H2 H4).
      apply le_n_S in H5. rewrite Nat.succ_pred in H5.
      apply (le_trans _ (0 + subseq n)). apply le_refl.
      apply Nat.add_le_mono_r. apply le_0_n.
      intro abs.
      destruct H2, H2. specialize (H2 n (S n) (le_refl _)).
      apply Nat.sub_0_le in abs. apply (le_not_lt _ _ abs).
      apply H2. apply le_n_S, H4.
      rewrite Nat.add_comm. apply Nat.lt_add_lt_sub_l.
      apply le_n_S in H5. rewrite Nat.succ_pred in H5. exact H5.
      intro abs.
      destruct H2, H2. specialize (H2 n (S n) (le_refl _)).
      apply Nat.sub_0_le in abs. apply (le_not_lt _ _ abs).
      apply H2. apply le_n_S, H4.
      rewrite sum_scale, CRmult_comm. apply CRmult_le_compat_l.
      apply CRlt_asym, epsPos.
      rewrite (TelescopicSum (fun i => ipt_seq Q (i + subseq n))).
      simpl.
      replace (S (pred (subseq (S n) - subseq n) + subseq n))
        with (subseq (S n)).
      destruct H2. rewrite H2. 2: apply le_n_S, H4. rewrite H2. apply CRle_refl.
      apply (le_trans _ _ _ H4). apply le_S, le_refl.
      replace (S (Init.Nat.pred (subseq (S n) - subseq n) + subseq n))
        with (S (Init.Nat.pred (subseq (S n) - subseq n)) + subseq n)%nat.
      2: reflexivity. rewrite Nat.succ_pred.
      rewrite Nat.sub_add. reflexivity.
      apply (le_trans _ (S (subseq n))). apply le_S, le_refl. apply H2.
      apply le_refl. apply le_n_S, H4.
      intro abs.
      destruct H2, H5.
      specialize (H5 n (S n) (le_refl _)).
      apply Nat.sub_0_le in abs. apply (le_not_lt _ _ abs), H5, le_n_S, H4.
    + rewrite (CRsum_eq _  (fun k : nat => (ipt_seq P (S k) - ipt_seq P k) * eps)).
      rewrite sum_scale, CRmult_comm. apply CRmult_le_compat_l.
      apply CRlt_asym, epsPos.
      rewrite TelescopicSum. destruct P; simpl.
      rewrite <- ipt_lastB0, <- ipt_head0. apply CRle_refl.
      intros. rewrite CRmult_comm. reflexivity.
  - apply CRplus_morph.
    + apply CRsum_eq. intros. apply CRmult_morph. reflexivity.
      rewrite (TelescopicSum (fun n => ipt_seq Q (n + subseq i))).
      simpl.
      replace (S (pred (subseq (S i) - subseq i) + subseq i))
        with (subseq (S i)).
      destruct H2. rewrite (H2 i). rewrite (H2 (S i)). reflexivity.
      apply le_n_S, H4. apply (le_trans _ _ _ H4), le_S, le_refl.
      replace (S (Init.Nat.pred (subseq (S i) - subseq i) + subseq i))
        with (S (Init.Nat.pred (subseq (S i) - subseq i)) + subseq i)%nat.
      2: reflexivity. rewrite Nat.succ_pred.
      rewrite Nat.sub_add. reflexivity.
      apply (le_trans _ (S (subseq i))). apply le_S, le_refl. apply H2.
      apply le_refl. apply le_n_S, H4.
      intro abs.
      destruct H2, H5.
      specialize (H5 i (S i) (le_refl _)).
      apply Nat.sub_0_le in abs. apply (le_not_lt _ _ abs), H5, le_n_S, H4.
    + unfold IntegralFiniteSum.
      rewrite partition_sum_by_packets. reflexivity. exact H2.
Qed.

Definition IntervalEquiPartition
           {R : ConstructiveReals} (a b : CRcarrier R) (last : nat)
  : a <= b -> @IntervalPartition R a b.
Proof.
  intros.
  apply (Build_IntervalPartition
           R a b
           (fun n:nat => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last).
  setoid_replace (Z.of_nat 0 # Pos.of_nat (S last))%Q with 0%Q.
  rewrite CR_of_Q_zero, CRmult_0_r, CRplus_0_r.
  reflexivity. reflexivity.
  setoid_replace (Z.of_nat (S last) # Pos.of_nat (S last))%Q with 1%Q.
  rewrite CR_of_Q_one, CRmult_1_r. unfold CRminus.
  rewrite CRplus_comm, CRplus_assoc, CRplus_opp_l.
  rewrite CRplus_0_r. reflexivity.
  unfold Qeq, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_l.
  rewrite <- positive_nat_Z, Nat2Pos.id. reflexivity. discriminate.
  intros. apply CRplus_le_compat_l.
  apply CRmult_le_compat_l.
  rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
  exact H. apply CRle_refl.
  apply CR_of_Q_le.
  unfold Qle, Qnum, Qden. apply Z.mul_le_mono_nonneg_r.
  discriminate. apply Nat2Z.inj_le, le_S, le_refl.
Defined.

Lemma WeavedListSelf : forall {R : ConstructiveReals} (xn : nat -> CRcarrier R) (last : nat),
    (forall n:nat, le n last -> (xn n) <= (xn (S n)))
    -> WeavedLists xn xn last.
Proof.
  intros R xn last H n H0.
  split. apply CRle_refl. apply H. exact H0.
Qed.

Lemma EquiPartitionMesh
  : forall {R : ConstructiveReals} (a b : CRcarrier R) (n last : nat) (leab : a <= b),
    PartitionMesh (ipt_seq (IntervalEquiPartition a b last leab)) (S n)
    == (b-a) * CR_of_Q R (1 # Pos.of_nat (S last)).
Proof.
  induction n.
  - intros. unfold PartitionMesh, IntervalEquiPartition, ipt_seq.
    setoid_replace (Z.of_nat 0 # Pos.of_nat (S last))%Q with 0%Q.
    2: reflexivity.
    rewrite CR_of_Q_zero, CRmult_0_r, CRplus_0_r.
    unfold CRminus. rewrite CRplus_assoc, <- (CRplus_comm (-a)), <- CRplus_assoc.
    rewrite CRplus_opp_r, CRplus_0_l.
    rewrite CRmax_left. reflexivity. rewrite <- (CRmult_0_r (b-a)).
    apply CRmult_le_compat_l.
    rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
    exact leab. apply CRle_refl.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  - intros.
    specialize (IHn last leab).
    unfold IntervalEquiPartition, ipt_seq.
    transitivity (CRmax ((a + (b - a) * CR_of_Q R (Z.of_nat (2+n) # Pos.of_nat (S last)))
                          - (a + (b - a) * CR_of_Q R (Z.of_nat (1+n) # Pos.of_nat (S last))))
                       (PartitionMesh (ipt_seq (IntervalEquiPartition a b last leab)) (S n))).
    reflexivity. rewrite IHn. clear IHn.
    setoid_replace (a + (b - a) * CR_of_Q R (Z.of_nat (2 + n) # Pos.of_nat (S last))
                        - (a + (b - a) * CR_of_Q R (Z.of_nat (1 + n) # Pos.of_nat (S last))))
      with ((b - a) * CR_of_Q R (1 # Pos.of_nat (S last))).
    rewrite CRmax_left. reflexivity. apply CRle_refl.
    rewrite CRplus_comm. unfold CRminus.
    rewrite CRopp_plus_distr, CRplus_assoc.
    rewrite <- (CRplus_assoc a), CRplus_opp_r, CRplus_0_l.
    rewrite CRopp_mult_distr_r, <- CRmult_plus_distr_l.
    apply CRmult_morph. reflexivity.
    rewrite <- CR_of_Q_opp, <- CR_of_Q_plus. apply CR_of_Q_morph.
    rewrite Qinv_minus_distr.
    unfold Qeq, Qnum, Qden. apply f_equal2. 2: reflexivity.
    simpl (2+n)%nat. rewrite (Nat2Z.inj_succ (S n)). unfold Z.succ.
    simpl (1+n)%nat. ring.
Qed.

Lemma UC_compare_integrals
  : forall {Re : ConstructiveReals} (f : CRcarrier Re -> CRcarrier Re)
      (a b eps epsR : CRcarrier Re)
      (cont_mod : forall eps:CRcarrier Re, 0 < eps -> CRcarrier Re)
      (P R Q : @IntervalPartition Re a b)
      (epsPos : 0 < eps) (epsPosR : 0 < epsR)
      (subseq : nat -> nat) (subseqR : nat -> nat),
    UniformCont f cont_mod
    -> IntervalPartitionRefinement _ _ P Q subseq
    -> IntervalPartitionRefinement _ _ R Q subseqR
    -> (PartitionMesh (ipt_seq P) (S (ipt_last P))) < (cont_mod eps epsPos)
    -> (PartitionMesh (ipt_seq R) (S (ipt_last R))) < (cont_mod epsR epsPosR)
    -> CRabs _ (IntegralFiniteSum f (ipt_seq P) (ipt_seq P) (ipt_last P)
                  - IntegralFiniteSum f (ipt_seq R) (ipt_seq R) (ipt_last R))
       <= (eps+epsR) * (b-a).
Proof.
  intros.
  setoid_replace (IntegralFiniteSum f (ipt_seq P) (ipt_seq P) (ipt_last P) -
                  IntegralFiniteSum f (ipt_seq R) (ipt_seq R) (ipt_last R))
    with (IntegralFiniteSum f (ipt_seq P) (ipt_seq P) (ipt_last P) -
          (IntegralFiniteSum f (ipt_seq Q) (ipt_seq Q) (ipt_last Q))
          + (IntegralFiniteSum f (ipt_seq Q) (ipt_seq Q) (ipt_last Q)
             - IntegralFiniteSum f (ipt_seq R) (ipt_seq R) (ipt_last R))).
  apply (CRle_trans _ _ _ (CRabs_triang _ _)).
  rewrite CRmult_plus_distr_r. apply CRplus_le_compat.
  - apply (UC_refine_integral
             f a b eps cont_mod
             _ _ _ _ epsPos subseq).
    exact H. apply WeavedListSelf, ipt_ordered.
    apply WeavedListSelf, ipt_ordered. exact H0. exact H2.
  - rewrite CRabs_minus_sym.
    apply (UC_refine_integral
             f a b epsR cont_mod
             _ _ _ _ epsPosR subseqR).
    exact H. apply WeavedListSelf, ipt_ordered.
    apply WeavedListSelf, ipt_ordered. exact H1. exact H3.
  - unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
    reflexivity. rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.

(* This definition can be generalized to function uniformly
   continuous on an interval. Just multiply f by a trapeze of
   height 1. *)
Lemma UC_integral_cauchy
  : forall {R : ConstructiveReals}
      (f : CRcarrier R -> CRcarrier R) (a b : CRcarrier R)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R),
    UniformCont f cont_mod
    -> a <= b
    -> CR_cauchy R
        (fun last : nat => IntegralFiniteSum
                        f (fun n => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
                        (fun n => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last).
Proof.
  intros. intros n.
  (* eps = / INR (S (2 * n)) * / (b - a) *)
  assert (0 < CR_of_Q R (Z.pos (2*n) # 1) * (1+b-a)) as invStepPos.
  { apply CRmult_lt_0_compat. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_lt. reflexivity.
    apply (CRlt_le_trans _ (1+0)). rewrite CRplus_0_r. apply CRzero_lt_one.
    unfold CRminus. rewrite CRplus_assoc. apply CRplus_le_compat_l.
    rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
    exact H0. apply CRle_refl. }
  assert (0 < CRinv R (CR_of_Q R (Z.pos (2*n) # 1) * (1+b-a))
                    (inr invStepPos)) as stepPos.
  { apply CRinv_0_lt_compat. exact invStepPos. }
  destruct H.
  destruct (CRup_nat ((b-a) * (CRinv R (cont_mod _ stepPos) (inr (c _ stepPos)))))
    as [p pmaj].
  exists p. intros.
  apply (CRle_trans
           _ (((CRinv R (CR_of_Q R (Z.pos (2*n) # 1) * (1+b-a)) (inr invStepPos))
               + (CRinv R (CR_of_Q R (Z.pos (2*n) # 1) * (1+b-a)) (inr invStepPos)))
              * (b-a))).
  assert (0 < S i * S j)%nat as sisjPos.
  { apply Nat.mul_pos_pos; apply le_n_S, le_0_n. }
  apply (UC_compare_integrals
           f a b
           (CRinv R (CR_of_Q R (Z.pos (2*n) # 1) * (1+b-a)) (inr invStepPos))
           (CRinv R (CR_of_Q R (Z.pos (2*n) # 1) * (1+b-a)) (inr invStepPos))
           cont_mod (IntervalEquiPartition a b i H0)
           (IntervalEquiPartition a b j H0)
           (IntervalEquiPartition a b (pred (S i * S j)) H0)
           stepPos stepPos (fun n => S j * n)%nat (fun n => S i * n)%nat).
  split; assumption.
  - split. intros. unfold IntervalEquiPartition, ipt_seq.
    rewrite Nat.succ_pred. apply CRplus_morph. reflexivity.
    apply CRmult_morph. reflexivity. apply CR_of_Q_morph.
    rewrite Nat2Z.inj_mul, Nat2Pos.inj_mul.
    unfold Qeq, Qnum, Qden. do 2 rewrite <- positive_nat_Z.
    rewrite Pos2Nat.inj_mul. rewrite Nat2Pos.id. rewrite Nat2Pos.id.
    rewrite Nat2Z.inj_mul. ring. discriminate. discriminate. discriminate.
    discriminate. discriminate.
    split.
    intros. apply Nat.mul_lt_mono_pos_l. apply le_n_S, le_0_n. exact H2.
    unfold IntervalEquiPartition, ipt_last.
    intros. rewrite Nat.succ_pred. rewrite Nat.mul_comm.
    apply Nat.mul_le_mono_nonneg_r. apply le_0_n. exact H2.
    intro abs. rewrite abs in sisjPos. inversion sisjPos.
  - split. intros. unfold IntervalEquiPartition, ipt_seq.
    rewrite Nat.succ_pred. apply CRplus_morph. reflexivity.
    apply CRmult_morph. reflexivity. apply CR_of_Q_morph.
    rewrite Nat2Z.inj_mul, Nat2Pos.inj_mul.
    unfold Qeq, Qnum, Qden. do 2 rewrite <- positive_nat_Z.
    rewrite Pos2Nat.inj_mul. rewrite Nat2Pos.id. rewrite Nat2Pos.id.
    rewrite Nat2Z.inj_mul. ring. discriminate. discriminate. discriminate.
    discriminate. discriminate.
    split.
    intros. apply Nat.mul_lt_mono_pos_l. apply le_n_S, le_0_n. exact H2.
    unfold IntervalEquiPartition, ipt_last.
    intros. rewrite Nat.succ_pred.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n. exact H2.
    intro abs. rewrite abs in sisjPos. inversion sisjPos.
  - rewrite EquiPartitionMesh.
    unfold IntervalEquiPartition, ipt_last.
    apply (CRle_lt_trans _ ((b - a) * CR_of_Q R (1 # Pos.of_nat (S p)))).
    apply CRmult_le_compat_l.
    rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
    exact H0. apply CRle_refl. apply CR_of_Q_le.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. rewrite Nat2Pos.id. apply le_n_S, H.
    discriminate. discriminate.
    apply (CRmult_lt_compat_r (cont_mod _ stepPos)) in pmaj.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r in pmaj.
    apply (CRmult_lt_reg_l (INR (S p))).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
    rewrite CRmult_comm, CRmult_assoc. unfold INR.
    rewrite <- CR_of_Q_mult.
    setoid_replace ((1 # Pos.of_nat (S p)) * (Z.of_nat (S p) # 1))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_r. apply (CRlt_le_trans _ _ _ pmaj).
    apply CRmult_le_compat_r. apply CRlt_asym, c.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
    apply Nat2Z.inj_le, le_S, le_refl.
    unfold Qmult, Qeq, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. rewrite Z.mul_1_r, <- positive_nat_Z.
    apply f_equal. rewrite Pos.mul_1_r. rewrite Nat2Pos.id.
    reflexivity. discriminate. apply c.
  - rewrite EquiPartitionMesh.
    unfold IntervalEquiPartition, ipt_last.
    apply (CRle_lt_trans _ ((b - a) * CR_of_Q R (1 # Pos.of_nat (S p)))).
    apply CRmult_le_compat_l.
    rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
    exact H0. apply CRle_refl. apply CR_of_Q_le.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. rewrite Nat2Pos.id. apply le_n_S, H1.
    discriminate. discriminate.
    apply (CRmult_lt_compat_r (cont_mod _ stepPos)) in pmaj.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r in pmaj.
    apply (CRmult_lt_reg_l (INR (S p))).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
    rewrite CRmult_comm, CRmult_assoc. unfold INR.
    rewrite <- CR_of_Q_mult.
    setoid_replace ((1 # Pos.of_nat (S p)) * (Z.of_nat (S p) # 1))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_r. apply (CRlt_le_trans _ _ _ pmaj).
    apply CRmult_le_compat_r. apply CRlt_asym, c.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
    apply Nat2Z.inj_le, le_S, le_refl.
    unfold Qmult, Qeq, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. rewrite Z.mul_1_r, <- positive_nat_Z.
    apply f_equal. rewrite Pos.mul_1_r. rewrite Nat2Pos.id.
    reflexivity. discriminate. apply c.
  - rewrite <- (CRmult_1_r
                 (CRinv R (CR_of_Q R (Z.pos (2 * n) # 1) * (1 + b - a)) (inr invStepPos))).
    rewrite <- CRmult_plus_distr_l.
    apply (CRmult_le_reg_l (CR_of_Q R (Z.pos (2 * n) # 1) * (1 + b - a))).
    exact invStepPos. do 2 rewrite <- CRmult_assoc.
    rewrite CRinv_r, CRmult_1_l.
    rewrite <- (CRmult_comm (1 + b - a)), CRmult_assoc.
    rewrite <- CR_of_Q_mult.
    setoid_replace ((Z.pos (2 * n) # 1) * (1 # n))%Q with 2%Q.
    rewrite CRmult_comm, <- CR_of_Q_one, <- CR_of_Q_plus.
    apply CRmult_le_compat_r. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate. rewrite CR_of_Q_one.
    rewrite <- (CRplus_0_l (b-a)).
    unfold CRminus. rewrite CRplus_assoc.
    apply CRplus_le_compat_r. apply CRlt_asym, CRzero_lt_one.
    unfold Qeq, Qnum, Qden. simpl. do 2 rewrite Pos.mul_1_r.
    reflexivity.
Qed.

Definition UC_integral {R : ConstructiveReals}
           (f : CRcarrier R -> CRcarrier R) (a b : CRcarrier R)
           (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
  : UniformCont f cont_mod
    -> a <= b
    -> CRcarrier R
  := fun H H0 => let (i,_) := CR_complete R (fun last : nat => IntegralFiniteSum
                        f (fun n => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
                        (fun n => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
                                            (UC_integral_cauchy f a b cont_mod H H0)
              in i.


(* Give the convergence speed of the integral more explicitly.
   This formula is useful for numerical computations of integrals
   in practice, to majorate the error. *)
Lemma UC_compare_integrals_limit
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (a b : CRcarrier R) (leab : a <= b) (n : nat)
      (eps : CRcarrier R) (epsPos : 0 < eps)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod),
    PartitionMesh (ipt_seq (IntervalEquiPartition a b n leab))
                       (S (ipt_last (IntervalEquiPartition a b n leab)))
    < cont_mod eps epsPos
    -> CRabs _ (IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b n leab))
                                     (ipt_seq (IntervalEquiPartition a b n leab))
                                     (ipt_last (IntervalEquiPartition a b n leab))
                  - UC_integral f a b cont_mod fCont leab)
       <= eps * (b-a).
Proof.
  intros.
  assert (forall k:nat, 0 < CR_of_Q R (1 # Pos.of_nat (S k))) as kPos.
  { intros. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. }
  assert (forall k:nat,
             let (q,_) := CRup_nat ((b-a) * (CRinv R (cont_mod _ (kPos k)) (inr ((fst fCont) _ (kPos k))))) in
             CRabs _
     (IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b n leab))
                        (ipt_seq (IntervalEquiPartition a b n leab)) (ipt_last (IntervalEquiPartition a b n leab))
      - IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b (max k q) leab))
                        (ipt_seq (IntervalEquiPartition a b (max k q) leab))
                        (ipt_last (IntervalEquiPartition a b (max k q) leab)))
           <= (eps + (CR_of_Q R (1# Pos.of_nat (S k)))) * (b-a)).
  { intro k.
    destruct (CRup_nat ((b-a) * (CRinv R (cont_mod _ (kPos k)) (inr ((fst fCont) _ (kPos k)))))) as [q qmaj].
    assert (0 < S n * S (max k q))%nat as sisjPos.
    apply Nat.mul_pos_pos; apply le_n_S, le_0_n.
    apply (UC_compare_integrals
             f a b _ _ cont_mod
             _ _ (IntervalEquiPartition a b (pred (S n * S (max k q))) leab)
             epsPos (kPos k) (fun i => S (max k q) * i)%nat (fun i => S n * i)%nat
             fCont).
    - split. intros. unfold IntervalEquiPartition, ipt_seq.
      rewrite Nat.succ_pred.
      apply CRplus_morph. reflexivity.
      apply CRmult_morph. reflexivity. apply CR_of_Q_morph.
      rewrite Nat2Z.inj_mul, Nat2Pos.inj_mul.
      unfold Qeq, Qnum, Qden. do 2 rewrite <- positive_nat_Z.
      rewrite Pos2Nat.inj_mul. rewrite Nat2Pos.id. rewrite Nat2Pos.id.
      rewrite Nat2Z.inj_mul. ring. discriminate. discriminate. discriminate.
      discriminate. discriminate.
      split.
      intros. apply Nat.mul_lt_mono_pos_l. apply le_n_S, le_0_n. exact H0.
      unfold IntervalEquiPartition, ipt_last.
      intros. rewrite Nat.succ_pred. rewrite Nat.mul_comm.
      apply Nat.mul_le_mono_nonneg_r. apply le_0_n. exact H0.
      intro abs. rewrite abs in sisjPos. inversion sisjPos.
    - split. intros. unfold IntervalEquiPartition, ipt_seq.
      rewrite Nat.succ_pred.
      apply CRplus_morph. reflexivity.
      apply CRmult_morph. reflexivity. apply CR_of_Q_morph.
      rewrite Nat2Z.inj_mul, Nat2Pos.inj_mul.
      unfold Qeq, Qnum, Qden. do 2 rewrite <- positive_nat_Z.
      rewrite Pos2Nat.inj_mul. rewrite Nat2Pos.id. rewrite Nat2Pos.id.
      rewrite Nat2Z.inj_mul. ring. discriminate. discriminate. discriminate.
      discriminate. discriminate.
      split.
      intros. apply Nat.mul_lt_mono_pos_l. apply le_n_S, le_0_n. exact H0.
      unfold IntervalEquiPartition, ipt_last.
      intros. rewrite Nat.succ_pred.
      apply Nat.mul_le_mono_nonneg_l. apply le_0_n. exact H0.
      intro abs. rewrite abs in sisjPos. inversion sisjPos.
    - exact H.
    - rewrite EquiPartitionMesh.
      apply (CRle_lt_trans _ ((b - a) * CR_of_Q R (1# Pos.of_nat (S q)))).
      apply CRmult_le_compat_l.
      rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
      exact leab. apply CRle_refl. apply CR_of_Q_le.
      unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
      apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
      rewrite Nat2Pos.id. rewrite Nat2Pos.id. apply le_n_S, Nat.le_max_r.
      discriminate. discriminate.
      apply (CRmult_lt_compat_r (cont_mod _ (kPos k))) in qmaj.
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r in qmaj.
      apply (CRmult_lt_reg_l (INR (S q))).
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
      rewrite CRmult_comm, CRmult_assoc. unfold INR.
      rewrite <- CR_of_Q_mult.
      setoid_replace ((1 # Pos.of_nat (S q)) * (Z.of_nat (S q) # 1))%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_r. apply (CRlt_le_trans _ _ _ qmaj).
      apply CRmult_le_compat_r. apply CRlt_asym. destruct fCont. apply c.
      apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
      apply Nat2Z.inj_le, le_S, le_refl.
      unfold Qmult, Qeq, Qnum, Qden.
      do 2 rewrite Z.mul_1_l. rewrite Z.mul_1_r, <- positive_nat_Z.
      apply f_equal. rewrite Pos.mul_1_r. rewrite Nat2Pos.id.
      reflexivity. discriminate. destruct fCont. apply c. }
  apply (CR_cv_le
           (fun k => let (q, _) :=
         CRup_nat
           ((b - a) *
            (CRinv R (cont_mod (CR_of_Q R (1 # Pos.of_nat (S k))) (kPos k))
              (inr (fst fCont (CR_of_Q R (1 # Pos.of_nat (S k))) (kPos k))))) in
       CRabs _
         (IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b n leab))
            (ipt_seq (IntervalEquiPartition a b n leab)) (ipt_last (IntervalEquiPartition a b n leab)) -
          IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b (Init.Nat.max k q) leab))
            (ipt_seq (IntervalEquiPartition a b (Init.Nat.max k q) leab))
            (ipt_last (IntervalEquiPartition a b (Init.Nat.max k q) leab))))
           (fun k => (eps + CR_of_Q R (1 # Pos.of_nat (S k))) * (b - a))).
  - intros. specialize (H0 n0).
    destruct (CRup_nat
       ((b - a) *
        (CRinv R (cont_mod (CR_of_Q R (1 # Pos.of_nat (S n0))) (kPos n0))
          (inr (fst fCont (CR_of_Q R (1 # Pos.of_nat (S n0))) (kPos n0)))))).
    exact H0.
  - intros eta. unfold UC_integral.
    destruct (CR_complete R
                  (fun last : nat =>
                   IntegralFiniteSum f
                     (fun n1 : nat => a + (b - a) * CR_of_Q R (Z.of_nat n1 # Pos.of_nat (S last)))
                     (fun n1 : nat => a + (b - a) * CR_of_Q R (Z.of_nat n1 # Pos.of_nat (S last))) last)
                  (UC_integral_cauchy f a b cont_mod fCont leab)).
    specialize (c eta) as [N u].
    exists N. intros n0 H1.
    destruct (CRup_nat
             ((b - a) *
              (CRinv R (cont_mod (CR_of_Q R (1 # Pos.of_nat (S n0))) (kPos n0))
                (inr (fst fCont (CR_of_Q R (1 # Pos.of_nat (S n0))) (kPos n0)))))).
    apply (CRle_trans _ _ _ (CRabs_triang_inv2 _ _)).
    setoid_replace (IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b n leab))
          (ipt_seq (IntervalEquiPartition a b n leab)) (ipt_last (IntervalEquiPartition a b n leab)) -
        IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b (Init.Nat.max n0 x0) leab))
          (ipt_seq (IntervalEquiPartition a b (Init.Nat.max n0 x0) leab))
          (ipt_last (IntervalEquiPartition a b (Init.Nat.max n0 x0) leab)) -
        (IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b n leab))
           (ipt_seq (IntervalEquiPartition a b n leab)) (ipt_last (IntervalEquiPartition a b n leab)) -
         x))
      with (-(IntegralFiniteSum f (ipt_seq (IntervalEquiPartition a b (Init.Nat.max n0 x0) leab))
          (ipt_seq (IntervalEquiPartition a b (Init.Nat.max n0 x0) leab))
          (ipt_last (IntervalEquiPartition a b (Init.Nat.max n0 x0) leab)) - x)).
    rewrite CRabs_opp. apply u.
    unfold IntervalEquiPartition, ipt_last.
    apply (le_trans _ _ _ H1), Nat.le_max_l.
    unfold CRminus. do 2 rewrite CRopp_plus_distr.
    rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
    rewrite CRplus_0_l. reflexivity.
  - apply CR_cv_scale. intros i.
    exists (Pos.to_nat i). intros.
    setoid_replace (eps + CR_of_Q R (1 # Pos.of_nat (S i0)) - eps)
      with (CR_of_Q R (1 # Pos.of_nat (S i0))).
    rewrite CRabs_right.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply (le_trans _ _ _ H1), le_S, le_refl.
    discriminate. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    unfold CRminus.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    reflexivity.
Qed.

Lemma UC_integral_translate
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (a b t : CRcarrier R) (leab : a <= b) (leabt : a+t <= b+t)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod),
    UC_integral f a b cont_mod fCont leab
    == UC_integral (fun x => f (x-t)) (a+t) (b+t) cont_mod
                   (UC_translate_horizontal f (-t) cont_mod fCont) leabt.
Proof.
  intros. unfold UC_integral.
  assert (forall i j k : CRcarrier R, i + j - (i + k) == j - k) as addSub.
  { intros. unfold CRminus. rewrite CRopp_plus_distr.
    rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity. }
  destruct (CR_complete R
       (fun last : nat =>
        IntegralFiniteSum (fun x : CRcarrier R => f (x - t))
          (fun n : nat => a + t + (b + t - (a + t)) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => a + t + (b + t - (a + t)) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          last)
       (UC_integral_cauchy (fun x : CRcarrier R => f (x - t)) (a + t) (b + t) cont_mod
                           (UC_translate_horizontal f (- t) cont_mod fCont) leabt)).
  apply (CR_cv_unique (fun last : nat =>
         IntegralFiniteSum (fun x : CRcarrier R => f (x - t))
           (fun n : nat => a + t + (b + t - (a + t)) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
           (fun n : nat => a + t + (b + t - (a + t)) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
           last)).
  2: exact c.
  destruct (CR_complete R
         (fun last : nat =>
          IntegralFiniteSum f
            (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
            (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
         (UC_integral_cauchy f a b cont_mod fCont leab)).
  apply (CR_cv_eq _ (fun last : nat =>
          IntegralFiniteSum f
            (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
            (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)).
  2: exact c0.
  intro n. apply CRsum_eq. intros. apply CRmult_morph.
  - apply (UniformContProper f cont_mod fCont).
    setoid_replace (b + t - (a + t)) with (b-a). unfold CRminus.
    do 2 rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    rewrite (CRplus_comm t), CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
    rewrite (CRplus_comm b), (CRplus_comm a). rewrite addSub. reflexivity.
  - setoid_replace (b + t - (a + t)) with (b-a). rewrite addSub, addSub. reflexivity.
    rewrite (CRplus_comm b), (CRplus_comm a). rewrite addSub. reflexivity.
Qed.

Lemma UC_integral_bound_proper :
  forall {R : ConstructiveReals}
    f (a b c d : CRcarrier R)
    (modF : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (fCont : UniformCont f modF)
    (leab : a <= b) (lecd : c <= d),
    a == c
    -> b == d
    -> UC_integral f a b modF fCont leab
      == UC_integral f c d modF fCont lecd.
Proof.
  intros. unfold UC_integral.
  destruct (CR_complete R
       (fun last : nat =>
        IntegralFiniteSum f
          (fun n : nat => c + (d - c) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => c + (d - c) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy f c d modF fCont lecd) ).
  apply (CR_cv_unique (fun last : nat =>
          IntegralFiniteSum f
            (fun n : nat => c + (d - c) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
            (fun n : nat => c + (d - c) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)).
  2: exact c0.
  destruct (CR_complete R
         (fun last : nat =>
          IntegralFiniteSum f
            (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
            (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
         (UC_integral_cauchy f a b modF fCont leab)).
  apply (CR_cv_eq _ (fun last : nat =>
          IntegralFiniteSum f
            (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
            (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)).
  2: exact c1.
  intro n. apply CRsum_eq. intros. clear c1 x0 c0 x.
  apply CRmult_morph. apply (UniformContProper f modF fCont).
  rewrite H, H0. reflexivity.
  rewrite H, H0. reflexivity.
Qed.

Lemma UC_right_bound_continuous
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (a b : CRcarrier R) (leab : a <= b)
      (eps : CRcarrier R) (epsPos : 0 < eps)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod),
    { eta : CRcarrier R
            & prod (0 < eta)
                   (forall (c:CRcarrier R) (leac : prod (b <= c) (c < b+eta)),
                       CRabs R (UC_integral f a b cont_mod fCont leab
                                - UC_integral f a c cont_mod fCont (CRle_trans a b c leab (fst leac)))
                       <= eps) }.
Proof.
  intros.
  (* When f is a constant function, its integral on [a,b] equals
     (b-a)f, so pushing b is weighted by f. *)
  destruct (UC_bounded f a b cont_mod fCont leab) as [B Bmaj].
  assert (forall i j k : CRcarrier R, i + j - (i + k) == j - k) as addSub.
  { intros. unfold CRminus. rewrite CRopp_plus_distr.
    rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity. }
  assert (0 < b-a+1).
  { rewrite <- (CRplus_opp_l a). unfold CRminus.
    rewrite (CRplus_comm b), CRplus_assoc. apply CRplus_lt_compat_l.
    apply (CRle_lt_trans _ (b+0)). rewrite CRplus_0_r. exact leab.
    apply CRplus_lt_compat_l, CRzero_lt_one. }
  assert (0 < B) as Bpos.
  { apply (CRle_lt_trans _ (CRabs R (f a))). apply CRabs_pos.
    apply Bmaj. apply CRle_refl. exact leab. }
  assert (0 < eps * CR_of_Q R (1#2) * CRinv R (b-a+1) (inr H)).
  { destruct fCont. apply CRmult_lt_0_compat. apply CRmult_lt_0_compat.
    exact epsPos. apply CR_of_Q_pos. reflexivity.
    apply CRinv_0_lt_compat, H. }
  exists (CRmin (cont_mod (eps * CR_of_Q R (1#2) * CRinv R (b-a+1) (inr H)) H0)
           (CRmin (eps * CR_of_Q R (1#2) * CRinv R B (inr Bpos)) 1)).
  split. apply CRmin_lt. apply (fst fCont). apply CRmin_lt.
  apply CRmult_lt_0_compat. apply CRmult_lt_0_compat. exact epsPos.
  apply CR_of_Q_pos. reflexivity. apply CRinv_0_lt_compat, Bpos.
  exact (CRzero_lt_one R). intros.
  apply (CR_cv_bound_up
           (fun last : nat => CRabs R (IntegralFiniteSum
                           f (fun n => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
                           (fun n => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last
                         - IntegralFiniteSum
                           f (fun n => a + (c-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
                           (fun n => a + (c-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last))
           eps _ O).
  - intros n _. unfold IntegralFiniteSum.
    unfold CRminus. rewrite <- sum_opp, <- sum_plus.
    rewrite (CRsum_eq _ (fun n0 => ((f (a + (b + - a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S n)))
                               * (b + - a)
                             - f (a + (c + - a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S n)))
                               * (c + - a)) * CR_of_Q R (1 # Pos.of_nat (S n))))).
    rewrite sum_scale, CRmult_comm.
    rewrite CRabs_mult, CRabs_right.
    2: rewrite <- CR_of_Q_zero; apply CR_of_Q_le; discriminate.
    apply (CRle_trans _ (CR_of_Q R (1 # Pos.of_nat (S n)) *
                         CRsum (fun k => CRabs R (f (a + (b + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n))) * (b-a) -
        f (a + (c + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n))) * (c-a))) n)).
    apply CRmult_le_compat_l.
    rewrite <- CR_of_Q_zero; apply CR_of_Q_le; discriminate.
    apply multiTriangleIneg.
    apply (CRle_trans _ (CR_of_Q R (1 # Pos.of_nat (S n)) * CRsum (fun _ => eps) n)).
    + (* Prove that each element of the sum is lower than eps. *)
      apply CRmult_le_compat_l.
      rewrite <- CR_of_Q_zero; apply CR_of_Q_le; discriminate.
      apply sum_Rle. intros.
      assert (CR_of_Q R (Z.of_nat k # Pos.of_nat (S n)) <= 1) as inInterval.
      { rewrite <- CR_of_Q_one. apply CR_of_Q_le.
        unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_l.
        destruct k. discriminate. unfold Z.of_nat.
        apply Pos2Z.pos_le_pos. rewrite Pos.of_nat_succ. apply Pos2Nat.inj_le.
        rewrite Nat2Pos.id, Nat2Pos.id. apply le_S, H1. discriminate. discriminate. }
      setoid_replace (f (a + (b + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n))) * (b - a) -
                      f (a + (c + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n))) * (c - a))
        with (f (a + (b + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n))) * (b - a) -
              f (a + (b + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n))) * (c - a) +
              (f (a + (b + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n))) * (c - a) -
               f (a + (c + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n))) * (c - a))).
      apply (CRle_trans _ _ _ (CRabs_triang _ _)).
      apply (CRle_trans _ (eps * CR_of_Q R (1#2) + eps * CR_of_Q R (1#2))).
      apply CRplus_le_compat.
      unfold CRminus. rewrite CRopp_mult_distr_r, <- CRmult_plus_distr_l, CRabs_mult.
      setoid_replace (b + - a + - (c + - a)) with (b-c).
      apply (CRle_trans _ (B * CRabs R (b-c))). apply CRmult_le_compat_r.
      apply CRabs_pos. apply CRlt_asym, Bmaj.
      apply (CRle_trans _ (a + 0)). rewrite CRplus_0_r. apply CRle_refl.
      apply CRplus_le_compat_l. apply CRmult_le_0_compat.
      rewrite <- (CRplus_opp_r a). apply CRplus_le_compat_r. exact leab.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le.
      unfold Qle; simpl. rewrite Z.mul_1_r. apply Nat2Z.is_nonneg.
      apply (CRplus_le_reg_l (-a)). rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      rewrite <- (CRmult_1_r (-a+b)), (CRplus_comm (-a)).
      apply CRmult_le_compat_l. rewrite <- (CRplus_opp_r a).
      apply CRplus_le_compat_r. exact leab. exact inInterval.
      rewrite CRabs_minus_sym, CRabs_right.
      apply (CRmult_le_reg_r (CRinv R B (inr Bpos))).
      apply CRinv_0_lt_compat, Bpos.
      rewrite CRmult_comm, <- CRmult_assoc, CRinv_l, CRmult_1_l.
      destruct leac. apply (CRplus_lt_compat_l R (-b)) in c1.
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_comm in c1.
      apply CRlt_asym, (CRlt_le_trans _ _ _ c1).
      apply (CRle_trans _ _ _ (CRmin_r _ _)). apply CRmin_l.
      rewrite <- (CRplus_opp_r b). apply CRplus_le_compat_r. exact (fst leac).
      do 2 rewrite <- (CRplus_comm (-a)). exact (addSub (-a) b c).
      unfold CRminus. rewrite CRopp_mult_distr_l, <- CRmult_plus_distr_r.
      rewrite CRabs_mult.
      apply (CRle_trans
               _ (eps * CR_of_Q R (1 # 2) * CRinv R (b - a + 1) (inr H) * CRabs R (c + - a))).
      apply CRmult_le_compat_r. apply CRabs_pos.
      apply CRlt_asym. apply (snd fCont _ _ _ H0). rewrite addSub.
      apply (CRle_lt_trans _ (c-b)).
      unfold CRminus. rewrite CRopp_mult_distr_l, <- CRmult_plus_distr_r, CRabs_mult.
      rewrite <- (CRplus_comm (-a)), <- (CRplus_comm (-a)), (addSub (-a) b c).
      rewrite <- (CRmult_1_r (c+-b)), CRabs_minus_sym, CRabs_right.
      apply CRmult_le_compat_l. rewrite <- (CRplus_opp_r b).
      apply CRplus_le_compat_r. exact (fst leac).
      rewrite CRabs_right. exact inInterval.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. unfold Qle; simpl.
      rewrite Z.mul_1_r. apply Nat2Z.is_nonneg.
      rewrite <- (CRplus_opp_r b).
      apply CRplus_le_compat_r. exact (fst leac).
      destruct leac. apply (CRplus_lt_compat_l R (-b)) in c1.
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_comm in c1.
      apply (CRlt_le_trans _ _ _ c1). apply CRmin_l.
      rewrite <- (CRmult_1_r (eps * CR_of_Q R (1 # 2))).
      do 2 rewrite CRmult_assoc. apply CRmult_le_compat_l. apply CRmult_le_0_compat.
      apply CRlt_asym, epsPos. apply CRlt_asym, CR_of_Q_pos. reflexivity.
      rewrite CRmult_1_l. apply (CRmult_le_reg_l (b-a+1) _ _ H).
      rewrite <- CRmult_assoc, CRinv_r, CRmult_1_l, CRmult_1_r.
      rewrite CRabs_right. unfold CRminus. rewrite (CRplus_comm c), (CRplus_comm b).
      rewrite CRplus_assoc. apply CRplus_le_compat_l.
      apply CRlt_asym. destruct leac. apply (CRlt_le_trans _ _ _ c1).
      apply CRplus_le_compat_l. apply (CRle_trans _ _ _ (CRmin_r _ _)), CRmin_r.
      rewrite <- (CRplus_opp_r a). apply CRplus_le_compat_r.
      apply (CRle_trans _ _ _ leab). exact (fst leac).
      rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus.
      rewrite Qinv_plus_distr. setoid_replace (1 + 1 # 2)%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_r. apply CRle_refl. reflexivity.
      unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
    + rewrite sum_const. rewrite CRmult_comm, CRmult_assoc.
      unfold INR. rewrite <- CR_of_Q_mult.
      setoid_replace ((Z.of_nat (S n) # 1) * (1 # Pos.of_nat (S n)))%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_r. apply CRle_refl.
      unfold Z.of_nat. rewrite Pos.of_nat_succ.
      unfold Qeq. simpl. do 2 rewrite Pos.mul_1_r. reflexivity.
    + intros. unfold CRminus. unfold CRminus in addSub.
      do 2 rewrite (addSub a).
      rewrite CRopp_mult_distr_r, <- CRmult_plus_distr_l.
      rewrite (CRopp_mult_distr_r (c+-a)), <- CRmult_plus_distr_l.
      setoid_replace (CR_of_Q R (Z.of_nat (S i) # Pos.of_nat (S n))
                      + - CR_of_Q R (Z.of_nat i # Pos.of_nat (S n)))
        with (CR_of_Q R (1 # Pos.of_nat (S n))).
      rewrite <- CRmult_assoc, <- CRmult_assoc, CRopp_mult_distr_l.
      rewrite <- CRmult_plus_distr_r. reflexivity.
      rewrite <- CR_of_Q_opp, <- CR_of_Q_plus. apply CR_of_Q_morph.
      rewrite Qinv_minus_distr.
      replace (Z.of_nat (S i) - Z.of_nat i)%Z with 1%Z. reflexivity.
      rewrite Nat2Z.inj_succ. unfold Z.succ. ring.
  - apply CR_cv_abs_cont. apply CR_cv_minus.
    unfold UC_integral.
    destruct (CR_complete R
         (fun last : nat =>
          IntegralFiniteSum f
            (fun n0 : nat => a + (b - a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last)))
            (fun n0 : nat => a + (b - a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last))) last)
         (UC_integral_cauchy f a b cont_mod fCont leab)).
    exact c0.
    unfold UC_integral.
    destruct (CR_complete R
         (fun last : nat =>
          IntegralFiniteSum f
            (fun n0 : nat => a + (c - a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last)))
            (fun n0 : nat => a + (c - a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last))) last)
         (UC_integral_cauchy f a c cont_mod fCont (CRle_trans a b c leab (fst leac)))).
    exact c0.
Qed.

Definition ConcatSequences {R : ConstructiveReals}
           (xn yn : nat -> CRcarrier R) (lenX n : nat) : CRcarrier R
  := if lt_dec n lenX then xn n else yn (n - lenX)%nat.

Definition IntervalPartitionConcat
           {R : ConstructiveReals} {a b c : CRcarrier R}
  : @IntervalPartition R a b
    -> @IntervalPartition R b c
    -> @IntervalPartition R a c.
Proof.
  intros P Q.
  apply (Build_IntervalPartition
           R a c
           (* do not count b twice *)
           (ConcatSequences (ipt_seq P) (ipt_seq Q) (S (ipt_last P)))
           (S (ipt_last P) + ipt_last Q)).
  - apply P.
  - unfold ConcatSequences.
    destruct (lt_dec (S (S (ipt_last P) + ipt_last Q)) (S (ipt_last P))).
    + exfalso. apply (lt_not_le _ _ l), le_n_S, (le_trans _ (S (ipt_last P) + 0)).
      rewrite Nat.add_0_r. apply le_S, le_refl. apply Nat.add_le_mono_l, le_0_n.
    + replace (S (S (ipt_last P) + ipt_last Q) - (S (ipt_last P)))%nat
        with (S (ipt_last Q)).
      apply Q. rewrite Nat.sub_succ. simpl plus.
      rewrite Nat.sub_succ_l. apply f_equal.
      rewrite Nat.add_comm, Nat.add_sub. reflexivity.
      apply (le_trans _ (ipt_last P + 0)). rewrite Nat.add_comm. apply le_refl.
      apply Nat.add_le_mono_l, le_0_n.
  - intros. unfold ConcatSequences.
    destruct (lt_dec (S n) (S (ipt_last P))).
    + destruct (lt_dec n (S (ipt_last P))). apply P, le_S_n, l0.
      exfalso. apply n0. apply le_S, le_S_n, l.
    + destruct (lt_dec n (S (ipt_last P))).
      apply (CRle_trans _ (ipt_seq P (S (ipt_last P)))).
      apply ipt_ordered_transit. apply le_S, le_S_n, l. apply le_refl.
      rewrite <- (ipt_lastB P). apply (CRle_trans _ (ipt_seq Q 0)).
      rewrite <- (ipt_head Q). apply CRle_refl. apply ipt_ordered_transit.
      apply le_0_n. simpl. apply Nat.le_sub_le_add_l.
      rewrite Nat.add_succ_r. exact H. clear n0.
      apply ipt_ordered_transit. apply Nat.le_sub_le_add_r.
      rewrite Nat.sub_add. apply le_S, le_refl.
      apply Nat.nlt_ge in n1. apply le_n_S, (le_trans _ (S (ipt_last P))).
      apply le_S, le_refl. exact n1. apply Nat.le_sub_le_add_r.
      simpl. apply le_n_S. rewrite Nat.add_comm. exact H.
Defined.

Definition IntervalPartitionConcatSum
  : forall {R : ConstructiveReals}
      (a b c : CRcarrier R) (f : CRcarrier R -> CRcarrier R)
      (P : @IntervalPartition R a b)
      (Q : @IntervalPartition R b c),
    IntegralFiniteSum f (ipt_seq P) (ipt_seq P) (ipt_last P)
    + IntegralFiniteSum f (ipt_seq Q) (ipt_seq Q) (ipt_last Q)
    == IntegralFiniteSum
        f (ipt_seq (IntervalPartitionConcat P Q))
        (ipt_seq (IntervalPartitionConcat P Q))
        (ipt_last (IntervalPartitionConcat P Q)).
Proof.
  intros. destruct P,Q; simpl. unfold IntegralFiniteSum.
  replace (S (ipt_last0 + ipt_last1)) with (S ipt_last0 + ipt_last1)%nat.
  2: reflexivity.
  rewrite sum_assoc. apply CRplus_morph.
  - apply CRsum_eq. intros. unfold ConcatSequences.
    destruct (lt_dec i (S ipt_last0)). clear l.
    2: apply le_n_S in H; contradiction.
    destruct (lt_dec (S i) (S ipt_last0)). reflexivity.
    apply CRmult_morph. reflexivity.
    apply CRplus_morph. 2: reflexivity.
    replace i with ipt_last0.
    + rewrite <- ipt_lastB0. rewrite Nat.sub_diag.
      rewrite <- ipt_head1. reflexivity.
    + apply le_antisym. apply le_S_n, Nat.nlt_ge, n. exact H.
  - apply CRsum_eq. intros. unfold ConcatSequences.
    destruct (lt_dec (S ipt_last0 + i) (S ipt_last0)).
    exfalso. apply (lt_not_le _ _ l).
    apply (le_trans _ (S ipt_last0 + 0)).
    rewrite Nat.add_0_r. apply le_refl. apply Nat.add_le_mono_l, le_0_n.
    clear n.
    destruct (lt_dec (S (S ipt_last0 + i)) (S ipt_last0)).
    exfalso. apply lt_not_le in l. apply l, le_n_S.
    apply (le_trans _ (S ipt_last0 + 0)).
    rewrite Nat.add_0_r. apply le_S, le_refl. apply Nat.add_le_mono_l, le_0_n.
    clear n.
    replace (S ipt_last0 + i - S ipt_last0)%nat with i.
    2: rewrite Nat.add_comm, Nat.add_sub; reflexivity.
    apply CRmult_morph. reflexivity.
    apply CRplus_morph. 2: reflexivity.
    replace (S (S ipt_last0 + i) - S ipt_last0)%nat with (S i).
    reflexivity.
    rewrite Nat.sub_succ. simpl plus.
    rewrite <- Nat.add_succ_r, Nat.add_comm, Nat.add_sub.
    reflexivity.
Qed.

(* The last point of the first list must be equal to
   the first point of the second list, otherwise the
   concatenation would introduce a parasite difference. *)
Lemma PartitionMeshConcat
  : forall {R : ConstructiveReals} (a b c : CRcarrier R)
      (P : @IntervalPartition R a b)
      (Q : @IntervalPartition R b c),
    PartitionMesh (ipt_seq (IntervalPartitionConcat P Q))
                  (S (ipt_last (IntervalPartitionConcat P Q)))
    == CRmax (PartitionMesh (ipt_seq P) (S (ipt_last P)))
           (PartitionMesh (ipt_seq Q) (S (ipt_last Q))).
Proof.
  intro R.
  assert (forall (xn yn : nat -> CRcarrier R) (p n : nat),
             xn n == yn O
             -> PartitionMesh (ConcatSequences xn yn n) (n + p)
               == CRmax (PartitionMesh xn n) (PartitionMesh yn p)).
  { induction p.
    - intros. unfold ConcatSequences.
      rewrite CRmax_left. 2: apply PartitionMesh_nonneg.
      rewrite Nat.add_0_r.
      rewrite (PartitionMesh_ext (fun n0 : nat => if lt_dec n0 n then xn n0 else yn (n0 - n)%nat) xn).
      reflexivity.
      intros. destruct (lt_dec n0 n). reflexivity.
      replace n0 with n. rewrite Nat.sub_diag. symmetry. exact H.
      apply le_antisym. 2: exact H0. apply Nat.nlt_ge. exact n1.
    - intros. rewrite Nat.add_succ_r. simpl.
      rewrite IHp. 2: exact H.
      assert (forall a b c : CRcarrier R,
                 CRmax a (CRmax b c) == CRmax b (CRmax a c)).
      intros. rewrite CRmax_assoc, (CRmax_sym a), <- CRmax_assoc. reflexivity.
      setoid_replace (ConcatSequences xn yn n (S (n + p)) - ConcatSequences xn yn n (n+p))
        with (yn (S p) - yn p).
      apply H0. unfold ConcatSequences.
      destruct (lt_dec (S (n + p)) n). exfalso. apply (lt_not_le _ _ l).
      apply (le_trans _ (S n + 0)). rewrite Nat.add_0_r. apply le_S, le_refl.
      simpl. apply le_n_S, Nat.add_le_mono_l, le_0_n.
      clear n0. destruct (lt_dec (n + p) n). exfalso. apply (lt_not_le _ _ l).
      apply (le_trans _ (n + 0)). rewrite Nat.add_0_r. apply le_refl.
      apply Nat.add_le_mono_l, le_0_n. clear n0.
      rewrite (Nat.add_comm n), Nat.add_sub. apply CRplus_morph.
      2: reflexivity.
      replace (S (p+n)) with (S p + n)%nat. 2: reflexivity.
      rewrite Nat.add_sub. reflexivity. }
  intros. unfold IntervalPartitionConcat, ipt_seq, ipt_last.
  destruct P, Q.
  replace (S (S ipt_last0 + ipt_last1))
    with (S ipt_last0 + S ipt_last1)%nat.
  rewrite H. apply CRmax_morph. reflexivity. reflexivity.
  rewrite <- ipt_lastB0. rewrite <- ipt_head1. reflexivity.
  rewrite Nat.add_succ_r. reflexivity.
Qed.

Fixpoint Fun2List (xn : nat -> Q) (len : nat) : list Q
  := match len with
     | O => Datatypes.nil
     | S p => Fun2List xn p ++ (Datatypes.cons (xn p) Datatypes.nil)
     end.

Lemma Fun2ListLength : forall (xn : nat -> Q) (len : nat),
    length (Fun2List xn len) = len.
Proof.
  induction len.
  - reflexivity.
  - simpl. rewrite app_length, IHlen, Nat.add_comm. reflexivity.
Qed.

Lemma Fun2ListNth : forall (xn : nat -> Q) (len n : nat),
    lt n len -> nth n (Fun2List xn len) 0%Q = xn n.
Proof.
  induction len.
  - intros. exfalso; inversion H.
  - intros. simpl. apply Nat.le_succ_r in H. destruct H.
    rewrite app_nth1. apply IHlen. exact H.
    rewrite Fun2ListLength. exact H. inversion H.
    rewrite app_nth2. rewrite Fun2ListLength, Nat.sub_diag.
    reflexivity. rewrite Fun2ListLength. apply le_refl.
Qed.

Definition IntervalPartitionRational
           {R : ConstructiveReals} {a b : CRcarrier R}
           (P : @IntervalPartition R a b)
  : Set
  := { rat : list Q
     | (length rat = plus 2 (ipt_last P))
       /\ forall n:nat, le n (S (ipt_last P)) -> ipt_seq P n == CR_of_Q R (nth n rat 0%Q) }.

Lemma EquiPartitionRational
  : forall {R : ConstructiveReals} (a b : Q) (k : nat)
      (leab : (CR_of_Q R a) <= (CR_of_Q R b)),
    IntervalPartitionRational (IntervalEquiPartition (CR_of_Q R a) (CR_of_Q R b) k leab).
Proof.
  intros. exists (Fun2List (fun n => a + (b-a) * (Z.of_nat n # Pos.of_nat (S k)))%Q (2+k)).
  intros. split.
  - rewrite Fun2ListLength. reflexivity.
  - intros. unfold IntervalEquiPartition, ipt_seq.
    unfold IntervalEquiPartition, ipt_last in H.
    rewrite Fun2ListNth. 2: apply le_n_S, H.
    rewrite CR_of_Q_plus. apply CRplus_morph. reflexivity.
    rewrite CR_of_Q_mult. unfold Qminus. rewrite CR_of_Q_plus, CR_of_Q_opp.
    reflexivity.
Qed.

Lemma PartitionRationalConcat
  : forall {R : ConstructiveReals} (a b c : CRcarrier R)
      (P : @IntervalPartition R a b)
      (Q : @IntervalPartition R b c),
    IntervalPartitionRational P
    -> IntervalPartitionRational Q
    -> IntervalPartitionRational (IntervalPartitionConcat P Q).
Proof.
  intros. destruct H, a0, H0, a0.
  exists (x ++ tl x0).
  intros. destruct P, Q; simpl; simpl in H, H2, H1, H0.
  split.
  - rewrite app_length, H. destruct x0.
    exfalso; inversion H0. simpl. simpl in H0. inversion H0.
    rewrite H4. rewrite Nat.add_succ_r. reflexivity.
  - intros. unfold ConcatSequences.
    destruct (lt_dec n (S ipt_last0)).
    + rewrite app_nth1. apply H1. apply le_S_n in l.
      apply (le_trans _ ipt_last0 _ l), le_S, le_refl.
      rewrite H. apply (lt_trans _ _ _ l), le_refl.
    + destruct (Nat.lt_trichotomy n (S ipt_last0)).
      contradiction. destruct H4. subst n.
      rewrite app_nth1. rewrite Nat.sub_diag, <- ipt_head1.
      rewrite <- H1. rewrite <- ipt_lastB0. reflexivity.
      apply le_refl. rewrite H. apply le_refl.
      clear n0. rewrite app_nth2, H.
      2: rewrite H; exact H4.
      destruct x0. exfalso; inversion H0. simpl.
      specialize (H2 (S(n - S (S(ipt_last0))))%nat). simpl in H2.
      rewrite <- H2.
      replace (n - S ipt_last0)%nat with (S (n - S (S ipt_last0))).
      reflexivity.
      rewrite (Nat.sub_succ_r _ (S ipt_last0)).
      rewrite Nat.succ_pred. reflexivity.
      intro abs. apply Nat.sub_0_le in abs.
      exact (lt_not_le _ _ H4 abs).
      rewrite (Nat.sub_succ_r _ (S ipt_last0)).
      rewrite Nat.succ_pred.
      rewrite Nat.le_sub_le_add_l, Nat.add_succ_r. exact H3.
      intro abs. apply Nat.sub_0_le in abs.
      exact (lt_not_le _ _ H4 abs).
Qed.

Lemma FunLocSorted : forall (xn : list Q),
    (forall n:nat, lt (S n) (length xn) -> Qle (nth n xn 0%Q) (nth (S n) xn 0%Q))
    -> LocallySorted (fun x x0 : QArith_base.Q => is_true (Qle_bool x x0)) xn.
Proof.
  induction xn.
  - intros. apply LSorted_nil.
  - intros. destruct xn. apply LSorted_cons1.
    apply LSorted_consn. apply IHxn.
    intros. apply (H (S n)). apply le_n_S, H0.
    unfold is_true. rewrite Qle_bool_iff. apply (H O).
    apply le_n_S, le_n_S, le_0_n.
Qed.

Lemma LocSortedFun : forall (xn : list Q),
    LocallySorted (fun x x0 : QArith_base.Q => is_true (Qle_bool x x0)) xn
    -> (forall n:nat, lt (S n) (length xn) -> Qle (nth n xn 0%Q) (nth (S n) xn 0%Q)).
Proof.
  induction xn.
  - intros. exfalso; inversion H0.
  - intros. simpl in H0.
    destruct xn. exfalso; inversion H0; inversion H2.
    destruct n. simpl. inversion H. unfold is_true in H5.
    rewrite Qle_bool_iff in H5. exact H5.
    apply IHxn. inversion H; exact H3.
    apply le_S_n in H0. exact H0.
Qed.

Lemma PartitionRationalLocSorted
  : forall {R : ConstructiveReals} (a b : CRcarrier R)
      (P : @IntervalPartition R a b)
      (rat : IntervalPartitionRational P),
    LocallySorted (fun x x0 : QArith_base.Q => is_true (Qle_bool x x0)) (proj1_sig rat).
Proof.
  intros. apply FunLocSorted.
  intros. destruct rat; simpl; unfold proj1_sig in H.
  destruct (Q_dec (nth n x 0) (nth (S n) x 0))%Q. destruct s.
  apply Qlt_le_weak, q. exfalso.
  destruct a0.
  rewrite H0 in H. apply le_S_n, le_S_n in H.
  apply (CR_of_Q_lt R) in q.
  rewrite <- H1 in q. rewrite <- (H1 n) in q. destruct P.
  simpl in q, H1. apply (ipt_ordered0 n). exact H. exact q.
  apply le_S, H. apply le_n_S, H.
  rewrite q. apply Qle_refl.
Qed.

Module QOrder <: TotalLeBool.
  Definition t := Q.
  Definition leb := Qle_bool.
  Theorem leb_total : forall a1 a2:Q, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros. unfold leb.
    do 2 rewrite Qle_bool_iff. destruct (Qlt_le_dec a1 a2).
    left. apply Qlt_le_weak, q. right. exact q.
  Qed.
End QOrder.

Module Import QSort := Sort QOrder.

Lemma MergeLength : forall (xn yn : list Q),
    length (merge xn yn) = plus (length xn) (length yn).
Proof.
  intros. pose proof (Permuted_merge xn yn).
  apply Permutation_length in H.
  rewrite <- H. apply app_length.
Qed.

(* index of xn n inside merge xn yn.
   Inner fixpoint allows to prove that recursive calls terminate. *)
Fixpoint MergeInjectL (xn yn : list Q) (n : nat) { struct xn } : nat
  := let fix merge_aux yn n :=
         match xn with
         | Datatypes.nil => O (* shouldn't happen *)
         | Datatypes.cons x tx
           => match yn with
             | Datatypes.nil => n
             | Datatypes.cons y ty
               => if Qlt_le_dec y x then
                   S (merge_aux ty n)
                 else (match n with O => O | S p => S (MergeInjectL tx yn p) end)
             end
         end
     in merge_aux yn n.

Lemma MergeInjectLSpec
  : forall (gas n : nat) (xn yn : list Q),
    lt (length xn + length yn) gas
    -> lt n (length xn)
    -> nth (MergeInjectL xn yn n) (merge xn yn) 0%Q
      = nth n xn 0%Q.
Proof.
  induction gas.
  - intros. exfalso; inversion H.
  - intros. destruct xn.
    + simpl. destruct yn. destruct n; reflexivity.
      exfalso; inversion H0.
    + destruct yn.
      simpl; destruct n; reflexivity. simpl.
      destruct (Qlt_le_dec q0 q).
      * destruct (Qle_bool q q0) eqn:des.
        exfalso. pose proof (Qle_bool_iff q q0) as [H1 _].
        apply (Qlt_not_le _ _ q1), H1, des.
        simpl. specialize (IHgas n (q :: xn) yn). simpl in IHgas.
        rewrite IHgas. reflexivity.
        simpl (length (q0 :: yn)) in H. rewrite Nat.add_succ_r in H.
        apply le_S_n in H. exact H. exact H0.
      * (* head of x first *)
        destruct n. (* equal q, no need of induction hypo *)
        destruct (Qle_bool q q0) eqn:des. reflexivity.
        exfalso. pose proof (Qle_bool_iff q q0) as [_ H1].
        rewrite H1 in des. discriminate. exact q1.
        specialize (IHgas n xn (q0 :: yn)).
        destruct (Qle_bool q q0) eqn:des.
        simpl. rewrite IHgas. reflexivity. simpl.
        simpl in H. apply le_S_n in H. exact H. simpl in H0.
        apply le_S_n in H0. exact H0.
        exfalso. pose proof (Qle_bool_iff q q0) as [_ H1].
        rewrite H1 in des. discriminate. exact q1.
Qed.

Lemma MergeInjectLInc
  : forall (gas n : nat) (xn yn : list Q),
    lt (length xn + length yn) gas
    -> lt (S n) (length xn)
    -> lt (MergeInjectL xn yn n) (MergeInjectL xn yn (S n)).
Proof.
  induction gas.
  - intros. exfalso; inversion H.
  - intros. destruct xn. exfalso; inversion H0.
    destruct yn. apply le_refl.
    simpl. destruct (Qlt_le_dec q0 q).
    + apply le_n_S. apply (IHgas n (q :: xn) yn).
      simpl in H. apply le_S_n in H. simpl. rewrite Nat.add_succ_r in H.
      exact H. exact H0.
    + destruct n. apply le_n_S, le_0_n. apply le_n_S.
      apply IHgas. simpl in H. apply le_S_n in H. exact H.
      simpl in H0. apply le_S_n in H0. exact H0.
Qed.

Lemma MergeInjectLBound
  : forall (gas n : nat) (xn yn : list Q),
    lt (length xn + length yn) gas
    -> lt n (length xn)
    -> lt (MergeInjectL xn yn n) (length xn + length yn).
Proof.
  induction gas.
  - intros. exfalso; inversion H.
  - intros. destruct xn. exfalso; inversion H0.
    destruct yn. simpl. rewrite Nat.add_0_r. exact H0.
    simpl. destruct (Qlt_le_dec q0 q).
    + apply le_n_S. specialize (IHgas n (q :: xn) yn).
      rewrite Nat.add_succ_r. apply IHgas. simpl in H.
      apply le_S_n in H. rewrite Nat.add_succ_r in H.
      exact H. exact H0.
    + destruct n. apply le_n_S, le_0_n. apply le_n_S.
      apply IHgas. simpl in H. apply le_S_n in H. exact H.
      simpl in H0. apply le_S_n in H0. exact H0.
Qed.

(* index of yn n inside merge xn yn.
   Inner fixpoint allows to prove that recursive calls terminate. *)
Fixpoint MergeInjectR (xn yn : list Q) (n : nat) { struct xn } : nat
  := let fix merge_aux yn n :=
         match xn with
         | Datatypes.nil => n
         | Datatypes.cons x tx
           => match yn with
             | Datatypes.nil => O (* shouldn't happen *)
             | Datatypes.cons y ty
               => if Qlt_le_dec y x then
                   (match n with O => O | S p => S (merge_aux ty p) end)
                 else S (MergeInjectR tx yn n)
             end
         end
     in merge_aux yn n.

Lemma MergeInjectRSpec
  : forall (gas n : nat) (xn yn : list Q),
    lt (length xn + length yn) gas
    -> lt n (length yn)
    -> nth (MergeInjectR xn yn n) (merge xn yn) 0%Q
      = nth n yn 0%Q.
Proof.
  induction gas.
  - intros. exfalso; inversion H.
  - intros. destruct xn.
    + simpl. destruct yn; reflexivity.
    + destruct yn. exfalso; inversion H0.
      simpl. destruct (Qlt_le_dec q0 q).
      * destruct n. destruct (Qle_bool q q0) eqn:des.
        exfalso. pose proof (Qle_bool_iff q q0) as [H1 _].
        apply (Qlt_not_le _ _ q1), H1, des. reflexivity.
        destruct (Qle_bool q q0) eqn:des.
        exfalso. pose proof (Qle_bool_iff q q0) as [H1 _].
        apply (Qlt_not_le _ _ q1), H1, des.
        specialize (IHgas n (q :: xn) yn). simpl. simpl in IHgas.
        rewrite IHgas. reflexivity. clear IHgas.
        simpl in H. apply le_S_n in H. rewrite Nat.add_succ_r in H.
        exact H. simpl in H0. apply le_S_n in H0. exact H0.
      * (* head of x first *)
        destruct (Qle_bool q q0) eqn:des.
        simpl. rewrite IHgas. reflexivity. simpl.
        simpl in H. apply le_S_n in H. exact H. simpl in H0.
        exact H0. exfalso. pose proof (Qle_bool_iff q q0) as [_ H1].
        rewrite H1 in des. discriminate. exact q1.
Qed.

Lemma MergeInjectRInc
  : forall (gas n : nat) (xn yn : list Q),
    lt (length xn + length yn) gas
    -> lt (S n) (length yn)
    -> lt (MergeInjectR xn yn n) (MergeInjectR xn yn (S n)).
Proof.
  induction gas.
  - intros. exfalso; inversion H.
  - intros. destruct yn as [|q0 yn]. exfalso; inversion H0.
    destruct xn as [|q xn]. apply le_refl.
    simpl. destruct (Qlt_le_dec q0 q).
    + destruct n. apply le_n_S, le_0_n. apply le_n_S.
      apply (IHgas n (q :: xn) yn).
      simpl in H. apply le_S_n in H. simpl. rewrite Nat.add_succ_r in H.
      exact H. simpl in H0. apply le_S_n in H0. exact H0.
    + apply le_n_S. apply IHgas.
      simpl in H. apply le_S_n in H. simpl.
      exact H. exact H0.
Qed.

Lemma MergeInjectRBound
  : forall (gas n : nat) (xn yn : list Q),
    lt (length xn + length yn) gas
    -> lt n (length yn)
    -> lt (MergeInjectR xn yn n) (length xn + length yn).
Proof.
  induction gas.
  - intros. exfalso; inversion H.
  - intros. destruct yn as [|q0 yn]. exfalso; inversion H0.
    destruct xn as [|q xn]. simpl. exact H0.
    simpl. destruct (Qlt_le_dec q0 q).
    + destruct n. apply le_n_S, le_0_n. apply le_n_S.
      rewrite Nat.add_succ_r.
      apply (IHgas n (q :: xn) yn). simpl in H.
      apply le_S_n in H. rewrite Nat.add_succ_r in H. exact H.
      simpl in H0. apply le_S_n in H0. exact H0.
    + apply le_n_S. apply (IHgas n xn (q0 :: yn)).
      simpl in H.
      apply le_S_n in H. exact H. exact H0.
Qed.

Lemma LastCons : forall (xn : list Q) (q : Q),
    lt 0 (length xn) -> last (q :: xn) 0%Q = last xn 0%Q.
Proof.
  intros. destruct xn. exfalso; inversion H. reflexivity.
Qed.

Lemma MergeLast : forall (gas : nat) (xn yn : list Q),
    lt (length xn + length yn) gas
    -> (lt 0 (length xn) \/ lt 0 (length yn))
    -> ((lt 0 (length xn) /\ last (merge xn yn) 0%Q = last xn 0%Q)
       \/ (lt 0 (length yn) /\ last (merge xn yn) 0%Q = last yn 0%Q)).
Proof.
  induction gas.
  - intros. exfalso; inversion H.
  - intros.
    destruct xn. right. split.
    destruct H0. exfalso; inversion H0. exact H0.
    destruct yn; reflexivity.
    (* xn not empty *)
    destruct yn. left.
    split. simpl. apply le_n_S, le_0_n. simpl. reflexivity.
    simpl. destruct (Qle_bool q q0) eqn:des.
    + specialize (IHgas xn (q0 :: yn)). simpl in IHgas.
      destruct IHgas.
      simpl in H. apply le_S_n in H. exact H.
      right. apply le_n_S, le_0_n.
      * destruct H1. left. split. apply le_n_S, le_0_n.
        rewrite LastCons.
        rewrite H2. destruct xn. exfalso; inversion H1. reflexivity.
        rewrite MergeLength. simpl.
        rewrite Nat.add_succ_r. apply le_n_S, le_0_n.
      * destruct H1 as [_ H1]. right. split.
        apply le_n_S, le_0_n. rewrite <- H1.
        pose proof (MergeLength xn (q0 :: yn)). simpl.
        destruct (merge xn (q0 :: yn)). exfalso. simpl in H2.
        rewrite Nat.add_succ_r in H2. discriminate. reflexivity.
    + specialize (IHgas (q :: xn) yn). destruct IHgas.
      simpl in H. apply le_S_n in H. rewrite Nat.add_succ_r in H.
      exact H. left. apply le_n_S, le_0_n.
      * destruct H1 as [_ H1]. left. split. apply le_n_S, le_0_n.
        rewrite LastCons. simpl in H1. rewrite H1. reflexivity.
        pose proof (MergeLength (q :: xn) yn). simpl in H2.
        rewrite H2. apply le_n_S, le_0_n.
      * destruct H1. right. split. apply le_n_S, le_0_n.
        rewrite LastCons. simpl in H2. rewrite H2.
        destruct yn. exfalso; inversion H1. reflexivity.
        pose proof (MergeLength (q :: xn) yn). simpl in H3.
        rewrite H3. apply le_n_S, le_0_n.
Qed.

Lemma LastNth : forall (xn : list Q),
    lt 0 (length xn)
    -> last xn 0%Q = nth (pred (length xn)) xn 0%Q.
Proof.
  induction xn.
  - reflexivity.
  - intros. clear H. destruct xn. reflexivity.
    transitivity (last (q :: xn) 0%Q). reflexivity.
    rewrite IHxn. reflexivity. simpl. apply le_n_S, le_0_n.
Qed.


Definition RationalPartitionMerge
           {R : ConstructiveReals} (a b : CRcarrier R)
           (P Q : @IntervalPartition R a b)
  : IntervalPartitionRational P
    -> IntervalPartitionRational Q
    -> @IntervalPartition R a b.
Proof.
  intros.
  apply (Build_IntervalPartition
           R a b (fun n:nat => CR_of_Q R (nth n (merge (proj1_sig H) (proj1_sig H0)) 0%Q))
           (2+ipt_last P + ipt_last Q)).
  - destruct H, H0; unfold proj1_sig.
    destruct a0, a1. destruct x. exfalso; inversion H.
    destruct x0. exfalso; inversion H1.
    specialize (H0 O). simpl in H0. specialize (H2 O). simpl in H2.
    simpl. destruct (Qle_bool q q0) eqn:des.
    + simpl. rewrite <- H0. apply P. apply le_0_n.
    + exfalso. assert (q == q0)%Q.
      apply (@eq_inject_Q R). rewrite <- H0, <- H2.
      transitivity a. symmetry. apply P. apply Q.
      apply le_0_n. apply le_0_n.
      rewrite <- H3 in des. clear H3.
      pose proof (Qle_bool_iff q q) as [_ H4]. rewrite H4 in des.
      discriminate. apply Qle_refl.
  - destruct H, H0; unfold proj1_sig.
    destruct a0, a1.
    destruct (MergeLast (S (2+ ipt_last P + (2+ipt_last Q))) x x0).
    rewrite H, H1. apply le_refl. left. rewrite H. apply le_n_S, le_0_n.
    + rewrite LastNth, MergeLength in H3.
      rewrite (LastNth x), H in H3.
      simpl in H3. transitivity (ipt_seq P (S (ipt_last P))).
      apply P. rewrite H0. 2: apply le_refl. apply CR_of_Q_morph.
      destruct H3. rewrite <- H4, H1.
      replace (ipt_last P + (2 + ipt_last Q))%nat
        with (2 + ipt_last P + ipt_last Q)%nat.
      reflexivity. rewrite (Nat.add_comm 2), Nat.add_assoc. reflexivity.
      rewrite H. apply le_n_S, le_0_n.
      rewrite MergeLength. apply (lt_trans _ (0 + length x0)).
      simpl. rewrite H1. apply le_n_S, le_0_n.
      apply Nat.add_lt_mono_r. rewrite H. apply le_n_S, le_0_n.
    + rewrite LastNth, MergeLength in H3.
      rewrite (LastNth x0), H1 in H3.
      simpl in H3. transitivity (ipt_seq Q (S (ipt_last Q))).
      apply Q. rewrite H2. 2: apply le_refl. apply CR_of_Q_morph.
      destruct H3. rewrite <- H4, H. simpl.
      replace (ipt_last P + S (S (ipt_last Q)))%nat
        with (2 + ipt_last P + ipt_last Q)%nat.
      reflexivity. rewrite (Nat.add_comm 2), <- Nat.add_assoc. reflexivity.
      rewrite H1. apply le_n_S, le_0_n.
      rewrite MergeLength. apply (lt_trans _ (0 + length x0)).
      simpl. rewrite H1. apply le_n_S, le_0_n.
      apply Nat.add_lt_mono_r. rewrite H. apply le_n_S, le_0_n.
  - pose proof (PartitionRationalLocSorted
                  a b P H) as sortP.
    pose proof (PartitionRationalLocSorted
                  a b Q H0) as sortQ.
    intros. apply CR_of_Q_le.
    destruct H, H0; unfold proj1_sig; unfold proj1_sig in sortP, sortQ.
    pose proof (Sorted_merge x x0 sortP sortQ).
    apply (LocSortedFun _ H n).
    rewrite MergeLength. destruct a0, a1. rewrite H0, H3.
    simpl. apply le_n_S, le_n_S. apply (le_trans _ _ _ H1).
    do 2 rewrite Nat.add_succ_r. apply le_refl.
Defined.

Lemma ordered_transit
  : forall (xn : nat -> nat) (last : nat),
    (forall n:nat, S n <= last -> xn n < xn (S n))%nat
    -> (forall n p:nat, lt n p -> p <= last -> (xn n < xn p))%nat.
Proof.
  induction p.
  - intros. exfalso. inversion H0.
  - intros. apply Nat.le_succ_r in H0. destruct H0.
    apply (lt_trans _ (xn p)). apply IHp. exact H0.
    apply (le_trans _ (S p)). apply le_S, le_refl. exact H1.
    apply H. exact H1. inversion H0. subst n.
    apply H. exact H1.
Qed.

Definition CommonChaslesRefinement
           {R : ConstructiveReals} {a b : CRcarrier R}
           (P Q : @IntervalPartition R a b)
  : Prop
  := exists (ccr_subseqP : nat -> nat) (ccr_subseqQ : nat -> nat)
       (ccr_refinement : @IntervalPartition R a b),
    IntervalPartitionRefinement
      a b P ccr_refinement ccr_subseqP
    /\ IntervalPartitionRefinement
        a b Q ccr_refinement ccr_subseqQ.

(* The rational numbers have a total order, which allows
   to merge 2 sorted lists. *)
Lemma CommonRationalRefinement
  : forall {R : ConstructiveReals} (a b : CRcarrier R)
      (P Q : @IntervalPartition R a b),
    IntervalPartitionRational P
    -> IntervalPartitionRational Q
    -> @CommonChaslesRefinement R a b P Q.
Proof.
  intros.
  exists (fun n => MergeInjectL (proj1_sig H) (proj1_sig H0) n),
  (fun n => MergeInjectR (proj1_sig H) (proj1_sig H0) n),
  (RationalPartitionMerge a b P Q H H0).
  split.
  - destruct H,H0; unfold proj1_sig.
    split. 2: split.
    + intros. unfold RationalPartitionMerge, ipt_seq; unfold proj1_sig.
      destruct P,Q; simpl in a0; unfold ipt_last in H; unfold ipt_last;
        unfold ipt_last, ipt_seq in a1.
      destruct a0, a1. rewrite H1. 2: exact H.
      apply CR_of_Q_morph.
      rewrite (MergeInjectLSpec (S (2 + ipt_last0 + (2+ ipt_last1)))).
      reflexivity.
      rewrite H0, H2. apply le_refl.
      rewrite H0. apply le_n_S, H.
    + apply ordered_transit. intros. destruct a0, a1.
      apply (MergeInjectLInc (S (2 + ipt_last P + (2+ ipt_last Q)))).
      rewrite H0, H2. apply le_refl.
      rewrite H0. apply le_n_S, H.
    + unfold RationalPartitionMerge, ipt_last.
      destruct P,Q; simpl in a0, a1.
      intros. destruct a0, a1. apply le_S_n.
      apply (le_trans _ (S (S ipt_last0) + S (S ipt_last1))).
      rewrite <- H0, <- H2.
      apply (MergeInjectLBound (S (2 + ipt_last0 + (2+ ipt_last1)))).
      rewrite H0, H2. apply le_refl.
      rewrite H0. apply le_n_S, H.
      simpl. do 2 rewrite Nat.add_succ_r. apply le_refl.
  - destruct H,H0; unfold proj1_sig.
    split. 2: split.
    + intros. unfold RationalPartitionMerge, ipt_seq; unfold proj1_sig.
      destruct P,Q; simpl in a0; unfold ipt_last in H; unfold ipt_last;
        unfold ipt_last, ipt_seq in a1.
      destruct a0, a1. rewrite H3. 2: exact H.
      apply CR_of_Q_morph.
      rewrite (MergeInjectRSpec (S (2 + ipt_last0 + (2+ ipt_last1)))).
      reflexivity.
      rewrite H0, H2. apply le_refl.
      rewrite H2. apply le_n_S, H.
    + apply ordered_transit. intros. destruct a0, a1.
      apply (MergeInjectRInc (S (2 + ipt_last P + (2+ ipt_last Q)))).
      rewrite H0, H2. apply le_refl.
      rewrite H2. apply le_n_S, H.
    + unfold RationalPartitionMerge, ipt_last.
      destruct P,Q; simpl in a0, a1.
      intros. destruct a0, a1. apply le_S_n.
      apply (le_trans _ (S (S ipt_last0) + S (S ipt_last1))).
      rewrite <- H0, <- H2.
      apply (MergeInjectRBound (S (2 + ipt_last0 + (2+ ipt_last1)))).
      rewrite H0, H2. apply le_refl.
      rewrite H2. apply le_n_S, H.
      simpl. do 2 rewrite Nat.add_succ_r. apply le_refl.
Qed.

(* Need a total order to merge partitions. Keep them rational for now,
   it is sufficient to bootstrap the constructive theory of measure. *)
Lemma UC_integral_chasles_rat
  : forall {R : ConstructiveReals} (a b c : Q)
      (f : CRcarrier R -> CRcarrier R)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod)
      (leab : (CR_of_Q R a) <= (CR_of_Q R b))
      (lebc : (CR_of_Q R b) <= (CR_of_Q R c))
      (leac : (CR_of_Q R a) <= (CR_of_Q R c)),
    UC_integral f (CR_of_Q R a) (CR_of_Q R c) cont_mod fCont leac
    == UC_integral f (CR_of_Q R a) (CR_of_Q R b) cont_mod fCont leab
      + UC_integral f (CR_of_Q R b) (CR_of_Q R c) cont_mod fCont lebc.
Proof.
  intros. unfold UC_integral.
  destruct (CR_complete R
       (fun last : nat =>
          IntegralFiniteSum
            f (fun n : nat => (CR_of_Q R a + (CR_of_Q R c - CR_of_Q R a)
                                            * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))))
            (fun n : nat => (CR_of_Q R a + (CR_of_Q R c - CR_of_Q R a)
                                          * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))) last)
       (UC_integral_cauchy f (CR_of_Q R a) (CR_of_Q R c) cont_mod fCont leac)) as [l lcv].
  destruct (CR_complete R
       (fun last : nat =>
        IntegralFiniteSum f
          (fun n : nat =>
           CR_of_Q R a + (CR_of_Q R b - CR_of_Q R a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat =>
           CR_of_Q R a + (CR_of_Q R b - CR_of_Q R a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy f (CR_of_Q R a) (CR_of_Q R b) cont_mod fCont leab)) as [lab H].
  destruct (CR_complete R
       (fun last : nat =>
        IntegralFiniteSum f
          (fun n : nat =>
           CR_of_Q R b + (CR_of_Q R c - CR_of_Q R b) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat =>
           CR_of_Q R b + (CR_of_Q R c - CR_of_Q R b) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy f (CR_of_Q R b) (CR_of_Q R c) cont_mod fCont lebc)) as [lbc H0].
  apply (CR_cv_unique _ _ _ lcv).
  intros n.
  assert (0 < 1+CR_of_Q R c - CR_of_Q R a) as invStepPos.
  { apply (CRlt_le_trans _ (1 + 0)).
    rewrite CRplus_0_r. apply CRzero_lt_one. unfold CRminus. rewrite CRplus_assoc.
    apply CRplus_le_compat_l. rewrite <- (CRplus_opp_r (CR_of_Q R a)).
    apply CRplus_le_compat. exact leac. apply CRle_refl. }
  assert (0 < CR_of_Q R (1 # 4*n) * CRinv R (1+CR_of_Q R c - CR_of_Q R a) (inr invStepPos))
    as stepPos.
  {  apply CRmult_lt_0_compat.
     rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
     apply CRinv_0_lt_compat. exact invStepPos. }
  destruct (CRup_nat ((CR_of_Q R c-CR_of_Q R a) * CRinv R (cont_mod _ stepPos) (inr ((fst fCont) _ stepPos))))
    as [p pmaj].
  destruct (CRup_nat ((CR_of_Q R b-CR_of_Q R a) * CRinv R (cont_mod _ stepPos) (inr ((fst fCont) _ stepPos))))
    as [q qmaj].
  destruct (CRup_nat ((CR_of_Q R c-CR_of_Q R b) * CRinv R (cont_mod _ stepPos) (inr ((fst fCont) _ stepPos))))
    as [r rmaj].
  specialize (H (4*n)%positive) as [i imaj].
  specialize (H0 (4*n)%positive) as [j jmaj].
  exists p. intros i0 H.
  pose (IntervalPartitionConcat
          (IntervalEquiPartition (CR_of_Q R a) (CR_of_Q R b) (max i q) leab)
          (IntervalEquiPartition (CR_of_Q R b) (CR_of_Q R c) (max j r) lebc))
    as conc.
  setoid_replace (IntegralFiniteSum f
       (fun n0 : nat =>
        CR_of_Q R a + (CR_of_Q R c - CR_of_Q R a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S i0)))
       (fun n0 : nat =>
        CR_of_Q R a + (CR_of_Q R c - CR_of_Q R a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S i0))) i0 -
                  (lab + lbc))
    with (IntegralFiniteSum f
       (fun n0 : nat =>
        CR_of_Q R a + (CR_of_Q R c - CR_of_Q R a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S i0)))
       (fun n0 : nat =>
          CR_of_Q R a + (CR_of_Q R c - CR_of_Q R a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S i0))) i0
          - IntegralFiniteSum f (ipt_seq conc) (ipt_seq conc) (ipt_last conc)
          + (IntegralFiniteSum f (ipt_seq conc) (ipt_seq conc) (ipt_last conc)
             - (lab + lbc))).
  apply (CRle_trans _ _ _ (CRabs_triang _ _)).
  setoid_replace (CR_of_Q R (1 # n))
    with (CR_of_Q R (1 # 2*n) + CR_of_Q R (1 # 2*n)).
  apply CRplus_le_compat.
  - apply (CRle_trans
             _ ((CR_of_Q R (1# 4*n) * CRinv R (1+CR_of_Q R c - CR_of_Q R a) (inr invStepPos)
                 + CR_of_Q R (1# 4*n) * CRinv R (1+CR_of_Q R c - CR_of_Q R a) (inr invStepPos))
                * (CR_of_Q R c-CR_of_Q R a))).
    destruct (CommonRationalRefinement
                (CR_of_Q R a) (CR_of_Q R c) (IntervalEquiPartition (CR_of_Q R a) (CR_of_Q R c) i0 leac) conc)
      as [ccr_subseqP0 [ccr_subseqQ0 [ccr_refinement0 [ccr_refineP0 ccr_refineQ0]]]].
    apply EquiPartitionRational. apply PartitionRationalConcat.
    apply EquiPartitionRational. apply EquiPartitionRational.
    apply (UC_compare_integrals
             f (CR_of_Q R a) (CR_of_Q R c) _ _
             cont_mod (IntervalEquiPartition (CR_of_Q R a) (CR_of_Q R c) i0 leac)
             conc ccr_refinement0
             stepPos stepPos ccr_subseqP0 ccr_subseqQ0
             fCont ccr_refineP0 ccr_refineQ0).
    + rewrite EquiPartitionMesh.
      apply (CRmult_lt_compat_r (cont_mod _ stepPos)) in pmaj.
      2: apply (fst fCont).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r in pmaj.
      apply (CRmult_lt_reg_r (CR_of_Q R (Z.of_nat (S i0) # 1))).
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # Pos.of_nat (S i0)) * (Z.of_nat (S i0) # 1))%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_r. apply (CRlt_le_trans _ _ _ pmaj).
      rewrite CRmult_comm. apply CRmult_le_compat_l.
      apply CRlt_asym, (fst fCont). apply CR_of_Q_le.
      unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, le_S, H.
      unfold Qmult, Qeq, Qnum, Qden.
      do 2 rewrite Z.mul_1_l. rewrite Z.mul_1_r, Pos.mul_1_r.
      rewrite <- positive_nat_Z. rewrite Nat2Pos.id. reflexivity. discriminate.
    + assert (PartitionMesh (ipt_seq conc) (S (ipt_last conc))
              == CRmax ((CR_of_Q R b- CR_of_Q R a) * CR_of_Q R (1# Pos.of_nat (S (max i q))))
                       ((CR_of_Q R c- CR_of_Q R b) * CR_of_Q R (1# Pos.of_nat (S (max j r))))).
      { unfold conc. rewrite PartitionMeshConcat.
        apply CRmax_morph; apply EquiPartitionMesh. }
      rewrite H0. apply CRmax_lub_lt.
      apply (CRmult_lt_compat_r (cont_mod _ stepPos)) in qmaj.
      2: apply (fst fCont).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r in qmaj.
      apply (CRmult_lt_reg_r
               (CR_of_Q R (Z.of_nat (S (Init.Nat.max i q)) # 1))).
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # Pos.of_nat (S (Init.Nat.max i q))) * (Z.of_nat (S (Init.Nat.max i q)) # 1))%Q
        with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_r. apply (CRlt_le_trans _ _ _ qmaj).
      rewrite CRmult_comm. apply CRmult_le_compat_l.
      apply CRlt_asym, (fst fCont). apply CR_of_Q_le.
      unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
      apply Nat2Z.inj_le, le_S, Nat.le_max_r.
      unfold Qmult, Qeq, Qnum, Qden.
      do 2 rewrite Z.mul_1_l. rewrite Z.mul_1_r, Pos.mul_1_r.
      rewrite <- positive_nat_Z. rewrite Nat2Pos.id. reflexivity. discriminate.

      apply (CRmult_lt_compat_r (cont_mod _ stepPos)) in rmaj.
      2: apply (fst fCont).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r in rmaj.
      apply (CRmult_lt_reg_r
               (CR_of_Q R (Z.of_nat (S (Init.Nat.max j r)) # 1))).
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # Pos.of_nat (S (Init.Nat.max j r))) * (Z.of_nat (S (Init.Nat.max j r)) # 1))%Q
        with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_r. apply (CRlt_le_trans _ _ _ rmaj).
      rewrite CRmult_comm. apply CRmult_le_compat_l.
      apply CRlt_asym, (fst fCont). apply CR_of_Q_le.
      unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
      apply Nat2Z.inj_le, le_S, Nat.le_max_r.
      unfold Qmult, Qeq, Qnum, Qden.
      do 2 rewrite Z.mul_1_l. rewrite Z.mul_1_r, Pos.mul_1_r.
      rewrite <- positive_nat_Z. rewrite Nat2Pos.id. reflexivity. discriminate.
    + rewrite <- (CRmult_1_r
                   (CR_of_Q R (1 # 4 * n) * CRinv R (1 + CR_of_Q R c - CR_of_Q R a) (inr invStepPos))).
      rewrite <- CRmult_plus_distr_l. rewrite (CRmult_comm (CR_of_Q R (1#4*n))).
      apply (CRmult_le_reg_l (1 + CR_of_Q R c - CR_of_Q R a)).
      exact invStepPos.
      do 3 rewrite <- CRmult_assoc. rewrite CRinv_r, CRmult_1_l.
      setoid_replace (CR_of_Q R (1 # 4 * n) * (1 + 1))
        with (CR_of_Q R (1 # 2 * n)).
      rewrite CRmult_comm. apply CRmult_le_compat_r.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- (CRplus_0_l (CR_of_Q R c - CR_of_Q R a)).
      unfold CRminus. rewrite CRplus_assoc.
      apply CRplus_le_compat_r.
      exact (CRlt_asym 0 1 (CRzero_lt_one R)).
      rewrite <- CR_of_Q_one, <- (CR_of_Q_plus R 1 1), <- CR_of_Q_mult.
      apply CR_of_Q_morph. unfold Qeq, Qnum, Qden. simpl.
      rewrite Pos.mul_1_r. reflexivity.
  - unfold conc.
    rewrite <- IntervalPartitionConcatSum.
    unfold IntervalEquiPartition, ipt_seq, ipt_last.
    setoid_replace (CR_of_Q R (1 # 2 * n))
      with (CR_of_Q R (1 # 4 * n) + CR_of_Q R (1 # 4 * n)).
    assert (forall a b c d : CRcarrier R,
               CRabs _ (a + b - (c + d)) <= CRabs _ (a - c) + CRabs _ (b - d)).
    intros.
    setoid_replace (a0 + b0 - (c0 + d)) with ((a0 - c0) + (b0 - d)).
    apply CRabs_triang. unfold CRminus.
    do 2 rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    rewrite (CRplus_comm (-c0)).
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    rewrite CRopp_plus_distr, CRplus_comm. reflexivity.
    apply (CRle_trans _ _ _ (H0 _ _ _ _)). apply CRplus_le_compat.
    apply imaj, Nat.le_max_l.
    apply jmaj, Nat.le_max_l.
    rewrite <- CR_of_Q_plus, Qinv_plus_distr. apply CR_of_Q_morph.
    reflexivity.
  - rewrite <- CR_of_Q_plus, Qinv_plus_distr. apply CR_of_Q_morph.
    reflexivity.
  - unfold CRminus. rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity.
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.

Lemma UC_right_bound_cv
  : forall {R : ConstructiveReals} (a b : CRcarrier R)
      (bn : nat -> CRcarrier R)
      (f : CRcarrier R -> CRcarrier R)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod)
      (leab : a <= b)
      (lebbn : forall n:nat, b <= bn n),
    CR_cv R bn b
    -> CR_cv R
            (fun n : nat =>
               UC_integral f a (bn n) cont_mod fCont
                           (CRle_trans a b (bn n) leab (lebbn n)))
            (UC_integral f a b cont_mod fCont leab).
Proof.
  intros. intro p.
  assert (0 < CR_of_Q R (1 # p)).
  { apply CR_of_Q_pos. reflexivity. }
  destruct (UC_right_bound_continuous
              f a b leab _ H0 cont_mod fCont) as [eta [etaPos etaMaj]].
  pose proof (Un_cv_nat_real _ _ H eta etaPos) as [n nmaj].
  exists n. intros. rewrite CRabs_minus_sym.
  assert (bn i < b + eta).
  { specialize (nmaj i H1). apply (CRplus_lt_reg_l R (-b)).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_comm.
    exact (CRle_lt_trans _ _ _ (CRle_abs _) nmaj). }
  apply (etaMaj (bn i) (pair (lebbn i) H2)).
Qed.

Lemma UC_integral_chasles_rat_rat
  : forall {R : ConstructiveReals} (a b : Q) (c : CRcarrier R)
      (f : CRcarrier R -> CRcarrier R)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod)
      (leab : (CR_of_Q R a) <= (CR_of_Q R b))
      (lebc : (CR_of_Q R b) <= c)
      (leac : (CR_of_Q R a) <= c),
    UC_integral f (CR_of_Q R a) c cont_mod fCont leac
    == UC_integral f (CR_of_Q R a) (CR_of_Q R b) cont_mod fCont leab
      + UC_integral f (CR_of_Q R b) c cont_mod fCont lebc.
Proof.
  intros.
  assert (forall n : nat, c < c + CR_of_Q R (1 # Pos.of_nat (S n))).
  { intro n. apply (CRle_lt_trans _ (c+0)). rewrite CRplus_0_r.
    apply CRle_refl. apply CRplus_lt_compat_l, CR_of_Q_pos. reflexivity. }
  pose (fun n => let (q,_) := CR_Q_dense R c (c + CR_of_Q R (1 # Pos.of_nat (S n))) (H n) in q)
    as cn.
  assert (forall n:nat, c <= CR_of_Q R (cn n)) as H0.
  { intro n. unfold cn.
    destruct (CR_Q_dense R c (c + CR_of_Q R (1 # Pos.of_nat (S n))) (H n)).
    apply CRlt_asym, p. }
  assert (CR_cv R (fun n : nat => CR_of_Q R (cn n)) c) as cvRight.
  { intro p. exists (Pos.to_nat p).
    intros. unfold cn.
    destruct (CR_Q_dense R c (c + CR_of_Q R (1 # Pos.of_nat (S i))) (H i)).
    rewrite CRabs_right.
    apply (CRplus_le_reg_r c). unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_comm.
    apply CRlt_asym, (CRlt_le_trans _ _ _ (snd p0)).
    apply CRplus_le_compat_l. apply CR_of_Q_le. apply Pos2Z.pos_le_pos.
    unfold Qden. do 2 rewrite Pos.mul_1_l. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply le_S, H1. discriminate.
    rewrite <- (CRplus_opp_r c). apply CRplus_le_compat_r.
    apply CRlt_asym, p0. }
  apply (CR_cv_unique (fun n => UC_integral f (CR_of_Q R a)
                                            (CR_of_Q R (cn n))
                                            cont_mod fCont
                                            (CRle_trans _ _ _ leac (H0 n)))).
  - apply (UC_right_bound_cv
             (CR_of_Q R a) c (fun n => CR_of_Q R (cn n)) f cont_mod fCont leac).
    exact cvRight.
  - apply (CR_cv_eq _ (fun n : nat =>
                         UC_integral f (CR_of_Q R a) (CR_of_Q R b) cont_mod fCont leab
                         + UC_integral f (CR_of_Q R b) (CR_of_Q R (cn n))
                                       cont_mod fCont (CRle_trans _ _ _ lebc (H0 n)))).
    intro n. symmetry.
    apply (UC_integral_chasles_rat a b (cn n) f).
    apply CR_cv_plus. apply CR_cv_const.
    exact (UC_right_bound_cv (CR_of_Q R b) c (fun n => CR_of_Q R (cn n)) f _ _ _ _ cvRight).
Qed.

Lemma UC_integral_slide_cv
  : forall {R : ConstructiveReals}
      (a b : CRcarrier R)
      (f : CRcarrier R -> CRcarrier R)
      (cont_mod : forall eps : CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod)
      (leab : a <= b)
      (an : nat -> CRcarrier R)
      (lebbn : forall n:nat, an n <= b + (an n - a)),
    CR_cv R an a
    -> CR_cv R
            (fun n : nat => UC_integral f (an n) (b + (an n - a))
                                   cont_mod fCont (lebbn n))
            (UC_integral f a b cont_mod fCont leab).
Proof.
  intros. intro p.
  assert (forall i j k : CRcarrier R, i + j - (i + k) == j - k) as addSub.
  { intros. unfold CRminus. rewrite CRopp_plus_distr.
    rewrite <- CRplus_assoc. apply CRplus_morph. 2: reflexivity.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity. }
  assert (0 < b-a+1).
  { rewrite <- (CRplus_opp_l a). unfold CRminus.
    rewrite (CRplus_comm b), CRplus_assoc. apply CRplus_lt_compat_l.
    apply (CRle_lt_trans _ (b+0)). rewrite CRplus_0_r. exact leab.
    apply CRplus_lt_compat_l, CRzero_lt_one. }
  assert (0 < CR_of_Q R (1#p) * CRinv R (b-a+1) (inr H0)) as H1.
  { destruct fCont. apply CRmult_lt_0_compat.
    apply CR_of_Q_pos. reflexivity.
    apply CRinv_0_lt_compat, H0. }
  pose proof (Un_cv_nat_real _ _ H _ (fst fCont _ H1)) as [n nmaj].
  exists n. intros.
  apply (CR_cv_bound_up
           (fun last : nat => CRabs R (IntegralFiniteSum
                           f (fun n => an i + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
                           (fun n => an i + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last
                         - IntegralFiniteSum
                           f (fun n => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
                           (fun n => a + (b-a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last))
           (CR_of_Q R (1#p)) _ O).
  - intros n0 _. unfold IntegralFiniteSum.
    unfold CRminus. rewrite <- sum_opp, <- sum_plus.
    rewrite (CRsum_eq _ (fun n1 => (f (an i + (b + - a) * CR_of_Q R (Z.of_nat n1 # Pos.of_nat (S n0)))
                               - f (a + (b + - a) * CR_of_Q R (Z.of_nat n1 # Pos.of_nat (S n0))))
                               * (b + - a) * CR_of_Q R (1 # Pos.of_nat (S n0)))).
    + rewrite sum_scale, sum_scale.
      specialize (nmaj i H2). rewrite CRmult_assoc, CRabs_mult.
      apply (CRle_trans
               _ ((CRsum (fun _ : nat => CR_of_Q R (1 # p) * CRinv R (b - a + 1) (inr H0)) n0) * CRabs R (CR_of_Q R (1 # Pos.of_nat (S n0)) * (b + - a)))).
      rewrite <- (CRmult_comm (b+-a)).
      apply CRmult_le_compat_r. apply CRabs_pos.
      apply (CRle_trans _ _ _ (multiTriangleIneg _ _)). apply sum_Rle.
      intros. apply CRlt_asym, (snd fCont _ _ _ H1).
      rewrite (CRplus_comm (an i)), (CRplus_comm a), addSub. exact nmaj.
      rewrite sum_const, CRabs_right,
      CRmult_assoc, <- (CRmult_1_r (CR_of_Q R (1 # p))).
      do 2 rewrite CRmult_assoc. apply CRmult_le_compat_l.
      apply CRlt_asym, CR_of_Q_pos. reflexivity. rewrite CRmult_1_l.
      unfold INR. rewrite CRmult_comm, <- CRmult_assoc. rewrite <- CR_of_Q_mult.
      setoid_replace ((Z.of_nat (S n0) # 1) * (1 # Pos.of_nat (S n0)))%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_l. apply (CRmult_le_reg_r (b-a+1) _ _ H0).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_1_l.
      apply (CRle_trans _ (b-a + 0)). rewrite CRplus_0_r. apply CRle_refl.
      apply CRplus_le_compat_l. apply CRlt_asym, CRzero_lt_one.
      unfold Z.of_nat. rewrite Pos.of_nat_succ.
      unfold Qeq. simpl. do 2 rewrite Pos.mul_1_r. reflexivity.
      apply CRmult_le_0_compat.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- (CRplus_opp_r a). apply CRplus_le_compat_r. exact leab.
    + intros.
      rewrite (addSub (an i) ((b + - a) * CR_of_Q R (Z.of_nat (S i0) # Pos.of_nat (S n0))) ((b + - a) * CR_of_Q R (Z.of_nat i0 # Pos.of_nat (S n0)))).
      rewrite (addSub a ((b + - a) * CR_of_Q R (Z.of_nat (S i0) # Pos.of_nat (S n0))) ((b + - a) * CR_of_Q R (Z.of_nat i0 # Pos.of_nat (S n0)))).
      rewrite CRopp_mult_distr_l, <- CRmult_plus_distr_r.
      unfold CRminus. rewrite CRopp_mult_distr_r, <- CRmult_plus_distr_l.
      rewrite CRmult_assoc. apply CRmult_morph. reflexivity.
      apply CRmult_morph. reflexivity.
      rewrite <- CR_of_Q_opp, <- CR_of_Q_plus. apply CR_of_Q_morph.
      rewrite Qinv_minus_distr.
      replace (Z.of_nat (S i0) - Z.of_nat i0)%Z with 1%Z. reflexivity.
      rewrite Nat2Z.inj_succ. unfold Z.succ. ring.
  - apply CR_cv_abs_cont. apply CR_cv_minus.
    unfold UC_integral.
    destruct (CR_complete R
         (fun last : nat =>
          IntegralFiniteSum f
            (fun n0 : nat => an i + (b + (an i - a) - an i) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last)))
            (fun n0 : nat => an i + (b + (an i - a) - an i) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last))) last)
         (UC_integral_cauchy f (an i) (b + (an i - a)) cont_mod fCont (lebbn i))).
    apply (CR_cv_eq _ (fun last : nat =>
         IntegralFiniteSum f
           (fun n0 : nat =>
            an i +
            (b + (an i - a) - an i) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last)))
           (fun n0 : nat =>
            an i +
            (b + (an i - a) - an i) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last)))
           last)).
    2: exact c. intros. apply CRsum_eq. intros.
    rewrite (UniformContProper f cont_mod fCont
                               _ (an i + (b - a) * CR_of_Q R (Z.of_nat i0 # Pos.of_nat (S n0)))).
    setoid_replace (b + (an i - a) - an i) with (b-a). reflexivity.
    unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
    reflexivity. rewrite CRplus_comm, <- CRplus_assoc.
    rewrite CRplus_opp_l. apply CRplus_0_l.
    apply CRplus_morph. reflexivity. apply CRmult_morph.
    2: reflexivity.
    unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
    reflexivity. rewrite CRplus_comm, <- CRplus_assoc.
    rewrite CRplus_opp_l. apply CRplus_0_l.
    unfold UC_integral.
    destruct (CR_complete R
         (fun last : nat =>
          IntegralFiniteSum f
            (fun n0 : nat => a + (b - a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last)))
            (fun n0 : nat => a + (b - a) * CR_of_Q R (Z.of_nat n0 # Pos.of_nat (S last))) last)
         (UC_integral_cauchy f a b cont_mod fCont leab)).
    exact c.
Qed.

Lemma UC_integral_chasles_rat_rat_rat
  : forall {R : ConstructiveReals} (a : Q) (b c : CRcarrier R)
      (f : CRcarrier R -> CRcarrier R)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod)
      (leab : (CR_of_Q R a) <= b)
      (lebc : b <= c)
      (leac : (CR_of_Q R a) <= c),
    UC_integral f (CR_of_Q R a) c cont_mod fCont leac
    == UC_integral f (CR_of_Q R a) b cont_mod fCont leab
      + UC_integral f b c cont_mod fCont lebc.
Proof.
  intros.
  assert (forall n : nat, b < b + CR_of_Q R (1 # Pos.of_nat (S n))).
  { intro n. apply (CRle_lt_trans _ (b+0)). rewrite CRplus_0_r.
    apply CRle_refl. apply CRplus_lt_compat_l, CR_of_Q_pos. reflexivity. }
  pose (fun n => let (q,_) := CR_Q_dense R b (b + CR_of_Q R (1 # Pos.of_nat (S n))) (H n) in q)
    as bn.
  assert (CR_cv R (fun n : nat => CR_of_Q R (bn n)) b) as cvb.
  { intro p. exists (Pos.to_nat p).
    intros. unfold bn.
    destruct (CR_Q_dense R b (b + CR_of_Q R (1 # Pos.of_nat (S i))) (H i)).
    rewrite CRabs_right.
    apply (CRplus_le_reg_r b). unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_comm.
    apply CRlt_asym, (CRlt_le_trans _ _ _ (snd p0)).
    apply CRplus_le_compat_l. apply CR_of_Q_le. apply Pos2Z.pos_le_pos.
    unfold Qden. do 2 rewrite Pos.mul_1_l. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply le_S, H0. discriminate.
    rewrite <- (CRplus_opp_r b). apply CRplus_le_compat_r.
    apply CRlt_asym, p0. }
  assert (forall n:nat, b <= CR_of_Q R (bn n)) as H0.
  { intro n. unfold bn.
    destruct (CR_Q_dense R b (b + CR_of_Q R (1 # Pos.of_nat (S n))) (H n)).
    apply CRlt_asym, p. }
  pose (fun n => c + (CR_of_Q R (bn n) - b)) as cn.
  assert (forall n:nat, CR_of_Q R (bn n) <= cn n).
  { intro n. unfold cn. rewrite CRplus_comm.
    apply (CRplus_le_reg_r (-c)).
    rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    apply CRplus_le_compat_l, CRopp_ge_le_contravar. exact lebc. }
  apply (CR_cv_unique (fun n => UC_integral f (CR_of_Q R a)
                                            (CR_of_Q R (bn n))
                                            cont_mod fCont
                                            (CRle_trans _ _ _ leab (H0 n))
                                + UC_integral f (CR_of_Q R (bn n)) (cn n)
                                            cont_mod fCont
                                            (H1 n))).
  - (* Use Chasles relation *)
    assert (forall n:nat, c <= cn n) as H2.
    { intro n. unfold cn.
      apply (CRle_trans _ (c+0)). rewrite CRplus_0_r. apply CRle_refl.
      apply CRplus_le_compat_l. rewrite <- (CRplus_opp_r b).
      apply CRplus_le_compat_r. apply H0. }
    apply (CR_cv_eq _ (fun n : nat =>
                         UC_integral f (CR_of_Q R a) (cn n) cont_mod fCont
                                     (CRle_trans _ _ _ leac (H2 n)))).
    intro n. apply UC_integral_chasles_rat_rat.
    apply UC_right_bound_cv. unfold cn.
    apply (CR_cv_proper _ (b+(c-b))).
    apply (CR_cv_eq _ (fun n : nat => CR_of_Q R (bn n) + (c - b))).
    intro n. rewrite (CRplus_comm c). unfold CRminus.
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    apply CRplus_comm. apply CR_cv_plus. exact cvb. apply CR_cv_const.
    unfold CRminus. rewrite CRplus_comm, CRplus_assoc, CRplus_opp_l.
    apply CRplus_0_r.
  - (* Split sum *)
    apply CR_cv_plus.
    + apply UC_right_bound_cv. exact cvb.
    + unfold cn.
      apply (UC_integral_slide_cv b c f cont_mod fCont lebc
                                  (fun n => CR_of_Q R (bn n))).
      exact cvb.
Qed.

Lemma UC_integral_chasles
  : forall {R : ConstructiveReals} (a b c : CRcarrier R)
      (f : CRcarrier R -> CRcarrier R)
      (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (fCont : UniformCont f cont_mod)
      (leab : a <= b) (lebc : b <= c) (leac : a <= c),
    UC_integral f a c cont_mod fCont leac
    == UC_integral f a b cont_mod fCont leab
      + UC_integral f b c cont_mod fCont lebc.
Proof.
  intros.
  assert (a-a <= c-a).
  { apply CRplus_le_compat_r, leac. }
  assert (CR_of_Q R 0 <= c-a).
  { rewrite CR_of_Q_zero, <- (CRplus_opp_r a). exact H. }
  rewrite (UC_integral_translate f a c (-a) _ H).
  rewrite (UC_integral_bound_proper
             _ (a+-a) (c+-a) (CR_of_Q R 0) (c+-a)
             cont_mod _ _ H0).
  assert (CR_of_Q R 0 <= b-a).
  { rewrite CR_of_Q_zero, <- (CRplus_opp_r a).
    apply CRplus_le_compat_r. exact leab. }
  assert (b-a <= c-a).
  { apply CRplus_le_compat_r. exact lebc. }
  rewrite (UC_integral_chasles_rat_rat_rat
             0 (b-a) (c+-a) _ _ _ H1 H2).
  apply CRplus_morph.
  - assert (a-a <= b-a).
    { apply CRplus_le_compat_r. exact leab. }
    rewrite (UC_integral_translate f a b (-a) _ H3).
    apply UC_integral_bound_proper.
    rewrite CRplus_opp_r, CR_of_Q_zero. reflexivity. reflexivity.
  - rewrite (UC_integral_translate f b c (-a) _ H2).
    apply UC_integral_bound_proper. reflexivity. reflexivity.
  - rewrite CRplus_opp_r, CR_of_Q_zero. reflexivity.
  - reflexivity.
Qed.

Lemma UC_integral_constant :
  forall {R : ConstructiveReals}
    f a b c (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (fCont : UniformCont f cont_mod) (leab : a <= b),
    (forall x, (a <= x /\ x <= b) -> f x == c)
    -> UC_integral f a b cont_mod fCont leab == (b-a) * c.
Proof.
  intros. unfold UC_integral.
  destruct (CR_complete R
       (fun last : nat =>
        IntegralFiniteSum f (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy f a b cont_mod fCont leab)).
  apply (CR_cv_unique
       (fun last : nat =>
          IntegralFiniteSum
            f (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))))
           (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))) last) ).
  exact c0. intros n.
  exists O. intros. unfold IntegralFiniteSum, CRminus.
  rewrite (CRsum_eq _ (fun k => c * (b-a) * CR_of_Q R (1# Pos.of_nat (S i)))).
  rewrite sum_const.
  setoid_replace (c * (b - a) * CR_of_Q R (1 # Pos.of_nat (S i)) * INR (S i) + - ((b + - a) * c))
    with (CRzero R).
  rewrite CRabs_right. rewrite <- CR_of_Q_zero. apply CR_of_Q_le; discriminate.
  apply CRle_refl. unfold INR.
  rewrite CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace ((1 # Pos.of_nat (S i)) * (Z.of_nat (S i) # 1))%Q with 1%Q.
  rewrite CR_of_Q_one, CRmult_1_r, CRmult_comm.
  unfold CRminus. rewrite CRplus_opp_r. reflexivity.
  unfold Qmult, Qeq, Qnum, Qden.
  do 2 rewrite Z.mul_1_l. rewrite Z.mul_1_r, Pos.mul_1_r.
  rewrite <- positive_nat_Z. rewrite Nat2Pos.id. reflexivity. discriminate.
  intros. rewrite H. rewrite CRmult_assoc.
  apply CRmult_morph. reflexivity.
  transitivity ((b + - a) * (CR_of_Q R (Z.of_nat (S i0) # Pos.of_nat (S i))
                             - CR_of_Q R (Z.of_nat i0 # Pos.of_nat (S i)))).
  unfold CRminus. do 3 rewrite CRmult_plus_distr_r.
  do 2 rewrite CRopp_plus_distr. do 2 rewrite CRmult_plus_distr_l.
  do 2 rewrite CRopp_mult_distr_l.
  do 4 rewrite <- CRplus_assoc.
  apply CRplus_morph.
  2: rewrite CRopp_involutive, <- CRopp_mult_distr_l,
     <- CRopp_mult_distr_r, CRopp_involutive; reflexivity.
  rewrite (CRplus_comm a). do 4 rewrite CRplus_assoc.
  apply CRplus_morph. reflexivity.
  do 2 rewrite <- CRplus_assoc.
  rewrite (CRplus_comm (b * - CR_of_Q R (Z.of_nat i0 # Pos.of_nat (S i)))).
  apply CRplus_morph. rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
  rewrite CRplus_0_l. reflexivity.
  rewrite <- CRopp_mult_distr_l, <- CRopp_mult_distr_r. reflexivity.
  apply CRmult_morph. reflexivity.
  unfold CRminus. rewrite <- CR_of_Q_opp, <- CR_of_Q_plus.
  apply CR_of_Q_morph. rewrite Qinv_minus_distr.
  replace (Z.of_nat (S i0) - Z.of_nat i0)%Z with 1%Z. reflexivity.
  rewrite Nat2Z.inj_succ. ring.

  split. apply (CRle_trans _ (a + 0)). rewrite CRplus_0_r. apply CRle_refl.
  apply CRplus_le_compat_l. rewrite <- (CRmult_0_r (b-a)).
  apply CRmult_le_compat_l.
  rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
  exact leab. apply CRle_refl.
  rewrite <- CR_of_Q_zero.
  apply CR_of_Q_le. unfold Qle, Qnum, Qden.
  rewrite Z.mul_0_l, Z.mul_1_r. apply Nat2Z.is_nonneg.
  apply (CRplus_le_reg_l (-a)).
  rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
  rewrite <- (CRmult_1_r (-a+b)), (CRplus_comm (-a)).
  apply CRmult_le_compat_l.
  rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
  exact leab. apply CRle_refl. rewrite <- CR_of_Q_one.
  apply CR_of_Q_le. unfold Qle, Qnum, Qden.
  rewrite Z.mul_1_r, Z.mul_1_l. rewrite <- positive_nat_Z.
  rewrite Nat2Pos.id. apply Nat2Z.inj_le, le_S, H1. discriminate.
Qed.

Lemma UC_integral_zero :
  forall {R : ConstructiveReals} f a b
    (cont_mod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (fCont : UniformCont f cont_mod) (leab : a <= b),
    (forall x, (a <= x /\ x <= b) -> f x == 0)
    -> UC_integral f a b cont_mod fCont leab == 0.
Proof.
  intros. rewrite (UC_integral_constant _ _ _ 0).
  rewrite CRmult_0_r. reflexivity. exact H.
Qed.

Lemma UC_integral_nonneg :
  forall {R : ConstructiveReals}
    f g a b (modF : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (modG : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (fCont : UniformCont f modF)
    (gCont : UniformCont g modG)
    (leab leabb : a <= b),
    (forall x, (a <= x /\ x <= b) -> (f x) <= (g x))
    -> UC_integral f a b modF fCont leab
       <= (UC_integral g a b modG gCont leabb).
Proof.
  intros. unfold UC_integral.
  destruct (CR_complete R
              (fun last : nat =>
        IntegralFiniteSum f (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy f a b modF fCont leab)).
  destruct (CR_complete R
              (fun last : nat =>
        IntegralFiniteSum g (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy g a b modG gCont leabb)).
  assert (forall n:nat, ((fun last : nat =>
         IntegralFiniteSum f (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))))
                           (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))) last) n)
                          <=
                     ((fun last : nat =>
          IntegralFiniteSum g (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))))
                            (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))) last) n)).
  { intros. unfold IntegralFiniteSum, CRminus.
    apply sum_Rle. intros. apply CRmult_le_compat_r.
    apply (CRle_minus
             (a + (b + - a) * CR_of_Q R (Z.of_nat k # Pos.of_nat (S n)))
             ( a + (b + - a) * CR_of_Q R (Z.of_nat (S k) # Pos.of_nat (S n)))).
    apply CRplus_le_compat_l.
    apply CRmult_le_compat_l.
    apply (CRle_minus a b), leab. apply CR_of_Q_le.
    unfold Qle, Qnum, Qden.
    apply Z.mul_le_mono_nonneg_r. discriminate.
    apply Nat2Z.inj_le, le_S, le_refl.
    apply H.
    split. apply (CRle_trans _ (a + 0)).
    rewrite CRplus_0_r. apply CRle_refl.
    apply CRplus_le_compat_l. rewrite <- (CRmult_0_r (b-a)).
    apply CRmult_le_compat_l.
    apply (CRle_minus a b), leab. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    rewrite Z.mul_0_l, Z.mul_1_r. apply Nat2Z.is_nonneg.
    apply (CRplus_le_reg_l (-a)).
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    rewrite <- (CRmult_1_r (-a+b)), (CRplus_comm (-a)).
    apply CRmult_le_compat_l.
    rewrite <- (CRplus_opp_r a). apply CRplus_le_compat.
    exact leab. apply CRle_refl. rewrite <- CR_of_Q_one.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    rewrite Z.mul_1_r, Z.mul_1_l. rewrite <- positive_nat_Z.
    rewrite Nat2Pos.id. apply Nat2Z.inj_le, le_S, H0. discriminate. }
  apply (CR_cv_le _ _ _ _ H0); assumption.
Qed.

Lemma UC_integral_pos :
  forall {R : ConstructiveReals}
    f a b (modF : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (fCont : UniformCont f modF)
    (leab : a <= b),
    (forall x, (a <= x /\ x <= b) -> 0 <= f x)
    -> 0 <= UC_integral f a b modF fCont leab.
Proof.
  intros.
  rewrite <- (UC_integral_zero (fun _ => 0) a b
                              (fun _ _ => 1) (UC_constant 0) leab).
  apply UC_integral_nonneg. exact H.
  intros. reflexivity.
Qed.

Lemma UC_integral_extens :
  forall {R : ConstructiveReals}
    f g a b (modF : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (modG : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (fCont : UniformCont f modF)
    (gCont : UniformCont g modG)
    (leab leabb : a <= b),
    (forall x, (a <= x /\ x <= b) -> f x == g x)
    -> UC_integral f a b modF fCont leab
      == UC_integral g a b modG gCont leabb.
Proof.
  intros. split; apply UC_integral_nonneg.
  intros. rewrite H. apply CRle_refl. exact H0.
  intros. rewrite H. apply CRle_refl. exact H0.
Qed.

Lemma UC_integral_extend_zero
  : forall {R : ConstructiveReals}
      (f : CRcarrier R -> CRcarrier R)
      (modF : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (a b c d : CRcarrier R) (fCont : UniformCont f modF)
      (leab : a <= b) (lecd : c <= d),
    c <= a
    -> b <= d
    -> (forall x : CRcarrier R, (c <= x /\ x <= a) -> f x == 0)
    -> (forall x : CRcarrier R, (b <= x /\ x <= d) -> f x == 0)
    -> UC_integral f a b modF fCont leab
      == UC_integral f c d modF fCont lecd.
Proof.
  intros.
  assert (a <= d).
  { apply (CRle_trans _ _ _ leab H0). }
  rewrite (UC_integral_chasles c a d f modF fCont H H3).
  rewrite (UC_integral_chasles a b d f modF fCont leab H0).
  rewrite (UC_integral_zero f c a).
  rewrite (UC_integral_zero f b d).
  rewrite CRplus_0_l, CRplus_0_r. reflexivity.
  exact H2. exact H1.
Qed.

Lemma UC_integral_extend_nonneg
  : forall {R : ConstructiveReals}
      (f : CRcarrier R -> CRcarrier R)
      (modF : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
      (a b c d : CRcarrier R) (fCont : UniformCont f modF)
      (leab : a <= b) (lecd : c <= d),
    c <= a
    -> b <= d
    -> (forall x : CRcarrier R, 0 <= (f x))
    -> UC_integral f a b modF fCont leab
       <= UC_integral f c d modF fCont lecd.
Proof.
  intros.
  assert (a <= d).
  { apply (CRle_trans _ _ _ leab). exact H0. }
  rewrite (UC_integral_chasles c a d f modF fCont H H2).
  rewrite (UC_integral_chasles a b d f modF fCont leab H0).
  apply (CRplus_le_reg_l (- UC_integral f a b modF fCont leab)).
  apply CRplus_le_compat_l. rewrite CRplus_comm.
  rewrite <- (CRplus_0_r (UC_integral f a b modF fCont leab)).
  do 2 rewrite CRplus_assoc. apply CRplus_le_compat_l.
  rewrite CRplus_0_l. rewrite <- (CRplus_0_r 0).
  apply CRplus_le_compat.
  apply UC_integral_pos. intros. apply H1.
  apply UC_integral_pos. intros. apply H1.
Qed.

Lemma UC_integral_plus :
  forall {R : ConstructiveReals}
    (f g : CRcarrier R -> CRcarrier R) (a b : CRcarrier R)
    (modF modG modS : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (fCont : UniformCont f modF)
    (gCont : UniformCont g modG)
    (sCont : UniformCont (fun x => (f x) + (g x)) modS)
    (leab leabb : a <= b),
    UC_integral (fun x => (f x) + (g x)) a b
                modS sCont leab
    == UC_integral f a b modF fCont leabb
       + UC_integral g a b modG gCont leabb.
Proof.
  intros.
  unfold UC_integral.
  destruct (CR_complete R
       (fun last : nat =>
        IntegralFiniteSum f (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy f a b modF fCont leabb)).
  destruct (CR_complete R
(fun last : nat =>
        IntegralFiniteSum g (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy g a b modG gCont leabb)).
  destruct (CR_complete R
(fun last : nat =>
        IntegralFiniteSum (fun x1 : CRcarrier R => f x1 + g x1)
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))) last)
       (UC_integral_cauchy (fun x1 : CRcarrier R => f x1 + g x1) a b modS sCont leab)).
  apply (CR_cv_unique _ _ _ c1).
  apply (CR_cv_eq
           _ (fun last : nat =>
          (IntegralFiniteSum f
            (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))))
            (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))) last)
          + (IntegralFiniteSum g
            (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))))
            (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))) last))).
  intro n. unfold IntegralFiniteSum. rewrite <- sum_plus.
  apply CRsum_eq.
  2: apply CR_cv_plus; assumption.
  intros.
  generalize (f (a + (b - a) * CR_of_Q R (Z.of_nat i # Pos.of_nat (S n)))),
  (g (a + (b - a) * CR_of_Q R (Z.of_nat i # Pos.of_nat (S n)))).
  intros.
  setoid_replace (a + (b - a) * CR_of_Q R (Z.of_nat (S i) # Pos.of_nat (S n)) -
   (a + (b - a) * CR_of_Q R (Z.of_nat i # Pos.of_nat (S n))))
    with ((b - a) * CR_of_Q R (Z.of_nat (S i) # Pos.of_nat (S n))
          - (b - a) * CR_of_Q R (Z.of_nat i # Pos.of_nat (S n))).
  rewrite <- CRmult_plus_distr_r. reflexivity.
  unfold CRminus. rewrite (CRplus_comm a), CRopp_plus_distr.
  rewrite CRplus_assoc, <- (CRplus_assoc a), CRplus_opp_r, CRplus_0_l.
  reflexivity.
Qed.

Lemma UC_integral_sum :
  forall {R : ConstructiveReals}
    (fn : nat -> CRcarrier R -> CRcarrier R) (a b : CRcarrier R) (n : nat)
    (modFn : forall (n:nat) (eps:CRcarrier R), 0 < eps -> CRcarrier R)
    (modSn : forall (eps:CRcarrier R), 0 < eps -> CRcarrier R)
    (fnCont : forall k:nat, UniformCont (fn k) (modFn k))
    (sCont : UniformCont (fun x => CRsum (fun k => (fn k x)) n) modSn)
    (leab : a <= b),
    UC_integral (fun x => CRsum (fun k => (fn k x)) n) a b
                modSn sCont leab
    == CRsum (fun k => UC_integral (fn k) a b (modFn k) (fnCont k) leab) n.
Proof.
  induction n.
  - intros. simpl. apply UC_integral_extens. intros. reflexivity.
  - intros. simpl.
    destruct (UC_sum fn modFn fnCont n) as [modS c].
    rewrite <- (IHn _ _ _ c). apply UC_integral_plus.
Qed.

Lemma Rcauchy_complete_eq
  : forall {R : ConstructiveReals} (xn : nat -> CRcarrier R)
      (cau : CR_cauchy R xn) (a : CRcarrier R),
    CR_cv R xn a
    -> (let (l,_) := CR_complete R xn cau in l) == a.
Proof.
  intros. destruct (CR_complete R xn cau).
  apply (CR_cv_unique xn); assumption.
Qed.

(* The partial integral sum equals a^2 * n/(2*(n+1))
   which converges to a^2/2. *)
Lemma x_RiemannInt : forall {R : ConstructiveReals} (a b : CRcarrier R) (leab : a <= b),
    UC_integral (fun x=> x) a b _ UC_x leab
    == (b*b - a*a) * CR_of_Q R (1#2).
Proof.
  intros. unfold UC_integral.
  apply Rcauchy_complete_eq.
  apply (CR_cv_eq _ (fun n => a*(b-a) + (CR_of_Q R (Z.of_nat n # Pos.of_nat (S n)))
                            * ((b-a) * (b-a) * CR_of_Q R (1#2)))).
  - intros. unfold IntegralFiniteSum.
    rewrite (CRsum_eq _ (fun k => a*(b-a) * CR_of_Q R (1# Pos.of_nat (S n))
                             + INR k * ((b-a)*(b-a) * CR_of_Q R (1# Pos.of_nat (S n * S n))))).
    + symmetry. rewrite sum_plus, sum_const.
      rewrite sum_scale, (CRmult_comm (CRsum (fun n0 => INR n0) n)).
      rewrite sum_INR.
      rewrite CRmult_assoc.
      setoid_replace (CR_of_Q R (1 # Pos.of_nat (S n)) * INR (S n)) with (CRone R).
      rewrite CRmult_1_r. apply CRplus_morph. reflexivity.
      rewrite <- (CRmult_comm ((b - a) * (b - a) * CR_of_Q R (1 # 2))).
      rewrite CRmult_assoc. rewrite (CRmult_assoc ((b-a)*(b-a))).
      apply CRmult_morph. reflexivity.
      rewrite CRmult_comm, (CRmult_comm ((INR n)*(INR (S n)))).
      rewrite (CRmult_assoc (CR_of_Q R (1#2))).
      apply CRmult_morph. reflexivity.
      unfold INR, CRealConstructive, CR_of_Q.
      do 2 rewrite <- CR_of_Q_mult. apply CR_of_Q_morph.
      rewrite Nat2Pos.inj_mul. unfold Qmult, Qeq, Qnum, Qden.
      rewrite Z.mul_1_r, Pos.mul_1_l.
      rewrite <- Z.mul_assoc. apply f_equal2. reflexivity.
      rewrite Pos2Z.inj_mul. apply f_equal2. 2: reflexivity.
      rewrite <- positive_nat_Z. rewrite Nat2Pos.id. reflexivity.
      discriminate. discriminate. discriminate.
      unfold INR. rewrite <- CR_of_Q_mult, <- CR_of_Q_one. apply CR_of_Q_morph.
      unfold Qmult, Qeq, Qnum, Qden. rewrite Pos.mul_1_r.
      rewrite Z.mul_1_l, Z.mul_1_l, Z.mul_1_r.
      rewrite <- positive_nat_Z. rewrite Nat2Pos.id. reflexivity.
      discriminate.
    + intros.
      setoid_replace (a + (b - a) * CR_of_Q R (Z.of_nat (S i) # Pos.of_nat (S n)) -
                          (a + (b - a) * CR_of_Q R (Z.of_nat i # Pos.of_nat (S n))))
        with ((b - a) * CR_of_Q R (1 # Pos.of_nat (S n))).
      rewrite CRmult_plus_distr_r. apply CRplus_morph.
      rewrite CRmult_assoc. reflexivity.
      unfold INR. rewrite Nat2Pos.inj_mul.
      setoid_replace (1 # Pos.of_nat (S n) * Pos.of_nat (S n))%Q
        with ((1 # Pos.of_nat (S n)) * (1 # Pos.of_nat (S n)))%Q.
      2: reflexivity. rewrite CR_of_Q_mult.
      setoid_replace (Z.of_nat i # Pos.of_nat (S n))%Q
        with ((Z.of_nat i # 1) * (1# Pos.of_nat (S n)))%Q.
      rewrite CR_of_Q_mult.
      do 4 rewrite <- CRmult_assoc. apply CRmult_morph.
      2: reflexivity. rewrite (CRmult_comm (b-a)).
      rewrite <- CRmult_assoc.
      do 2 rewrite (CRmult_assoc (CR_of_Q R (Z.of_nat i # 1) * (b - a))).
      apply CRmult_morph. reflexivity. apply CRmult_comm.
      unfold Qmult, Qeq, Qnum, Qden. rewrite Z.mul_1_r. reflexivity.
      discriminate. discriminate.
      setoid_replace (Z.of_nat (S i) # Pos.of_nat (S n))%Q
        with ((1#Pos.of_nat (S n)) + (Z.of_nat i # Pos.of_nat (S n)))%Q.
      rewrite CR_of_Q_plus. unfold CRminus. rewrite CRopp_plus_distr.
      rewrite <- CRplus_assoc, (CRplus_comm a).
      do 2 rewrite CRplus_assoc. rewrite <- (CRplus_assoc a).
      rewrite CRplus_opp_r, CRplus_0_l, CRopp_mult_distr_r.
      rewrite <- CRmult_plus_distr_l. apply CRmult_morph. reflexivity.
      rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r. reflexivity.
      rewrite Qinv_plus_distr. fold (1 + i)%nat.
      rewrite Nat2Z.inj_add. reflexivity.
  - apply (CR_cv_proper
             _ (a*(b-a) + 1 * ((b-a) * (b-a) * CR_of_Q R (1#2)))).
    apply (CR_cv_plus _ _ (a*(b-a))).
    apply CR_cv_const. apply CR_cv_scale.
    intros n. exists (Pos.to_nat n). intros.
    rewrite CRabs_minus_sym.
    setoid_replace (1 - CR_of_Q R (Z.of_nat i # Pos.of_nat (S i)))
      with (CR_of_Q R (1# Pos.of_nat (S i))).
    rewrite CRabs_right. apply CR_of_Q_le.
    unfold Qle,Qnum,Qden. do 2 rewrite Z.mul_1_l.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id. apply le_S,H. discriminate.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le; discriminate.
    unfold CRminus. rewrite <- CR_of_Q_one, <- CR_of_Q_opp, <- CR_of_Q_plus.
    apply CR_of_Q_morph. unfold Qopp,Qplus,Qeq,Qnum,Qden.
    apply f_equal2. 2: reflexivity.
    rewrite Z.mul_1_l, Z.mul_1_r.
    rewrite <- positive_nat_Z, Nat2Pos.id. 2: discriminate.
    fold (1+i)%nat. rewrite Nat2Z.inj_add. ring.
    rewrite CRmult_1_l.
    rewrite (CRmult_comm a), CRmult_assoc, <- CRmult_plus_distr_l.
    setoid_replace (a + (b - a) * CR_of_Q R (1 # 2))
      with ((a+b) * CR_of_Q R (1#2)).
    rewrite <- CRmult_assoc. apply CRmult_morph. 2: reflexivity.
    unfold CRminus. rewrite CRmult_plus_distr_r, CRmult_plus_distr_l.
    rewrite CRmult_plus_distr_l, (CRplus_comm (b*a)), CRplus_assoc.
    apply CRplus_morph. reflexivity. rewrite CRplus_comm.
    rewrite <- (CRopp_mult_distr_l a b), (CRmult_comm a b).
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite <- CRopp_mult_distr_l. reflexivity.
    apply (CRmult_eq_reg_r (CR_of_Q R 2)).
    left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt; reflexivity.
    rewrite CRmult_plus_distr_r.
    rewrite CRmult_assoc, CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1#2)*2)%Q with 1%Q. 2: reflexivity.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_1_r, CRmult_1_r.
    rewrite CRmult_plus_distr_l. rewrite CRmult_1_r. rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity. unfold CRminus.
    rewrite CRplus_comm, CRplus_assoc, CRplus_opp_l.
    apply CRplus_0_r.
Qed.

Lemma UC_integral_scale :
  forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
    (a b l : CRcarrier R)
    (modF : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
    (fCont : UniformCont f modF) (leab : a <= b),
    UC_integral (fun x => l * (f x)) a b
                  _ (UC_scale f modF l fCont) leab
    == l * (UC_integral f a b modF fCont leab).
Proof.
  intros.
  unfold UC_integral.
  destruct (CR_complete R
       (fun last : nat =>
        IntegralFiniteSum f
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          (fun n : nat => a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))
          last) (UC_integral_cauchy f a b modF fCont leab)).
  apply Rcauchy_complete_eq.
  apply (CR_cv_eq
           _ (fun last : nat =>
          (IntegralFiniteSum f
            (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last))))
            (fun n : nat => (a + (b - a) * CR_of_Q R (Z.of_nat n # Pos.of_nat (S last)))) last) * l)).
  2: rewrite CRmult_comm; apply CR_cv_scale, c.
  intro n. unfold IntegralFiniteSum.
  rewrite <- sum_scale. apply CRsum_eq.
  intros.
  rewrite (CRmult_comm l). do 2 rewrite CRmult_assoc. apply CRmult_morph.
  reflexivity. apply CRmult_comm.
Qed.

Lemma TrapezeLe : forall {R : ConstructiveReals} (a b eta : CRcarrier R)
                    (etaPos : 0 < eta),
    a <= b -> a-eta <= b+eta.
Proof.
  intros. apply (CRle_trans _ (a-0)).
  apply CRplus_le_compat_l, CRopp_ge_le_contravar, CRlt_asym, etaPos.
  unfold CRminus. rewrite CRopp_0. apply CRplus_le_compat.
  exact H. apply CRlt_asym, etaPos.
Qed.

Lemma CSUCUnitTrapezeInt
  : forall {R : ConstructiveReals}
      (a b eta : CRcarrier R) (etaPos : 0 < eta) (leab : a <= b),
    UC_integral (CSUCUnitTrapeze a b eta etaPos)
                (a-eta) (b+eta)
                _ (CSUCUnitTrapeze_cont a b eta etaPos leab)
                (TrapezeLe a b eta etaPos leab)
    == eta + b - a.
Proof.
  intros.
  assert (a-eta <= a).
  { apply (CRle_trans _ (a-0)).
    apply CRplus_le_compat_l, CRopp_ge_le_contravar, CRlt_asym, etaPos.
    unfold CRminus. rewrite CRopp_0, CRplus_0_r. apply CRle_refl. }
  assert (b <= b+eta) as H1.
  { apply (CRplus_le_reg_l (-b)).
    rewrite CRplus_opp_l, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    apply CRlt_asym, etaPos. }
  assert (a <= b+eta).
  { apply (CRle_trans _ b _ leab). exact H1. }
  rewrite (UC_integral_chasles
             (a-eta) a (b+eta)
             (CSUCUnitTrapeze a b eta etaPos)
             _ _ H H0).
  rewrite (UC_integral_chasles
             a b (b+eta)
             (CSUCUnitTrapeze a b eta etaPos)
             _ _ leab H1).
   assert (forall t:CRcarrier R, UniformCont (fun x => x + t) (fun eps epsPos => eps)) as H2.
   { intro t. apply (UC_translate_horizontal (fun x=>x) t). apply UC_x. }
  rewrite (UC_integral_extens
             _ (fun x:CRcarrier R => CRinv R eta (inr etaPos) * (x + (eta - a)))
             (a - eta) a
             _ _ _ (UC_scale _ _ _ (H2 _)) H H).
  rewrite (UC_integral_extens
             _ (fun x:CRcarrier R => 1) a b
             _ (fun eps epsPos => 1) _ (UC_constant _) leab leab).
  rewrite (UC_integral_extens
             _ (fun x:CRcarrier R => (-CRinv R eta (inr etaPos))
                                    * (x + (- b - eta)))
             b (b+eta) _ _
             _ (UC_scale _ _ (-CRinv R eta (inr etaPos)) (H2 _)) H1 H1).
  - rewrite (UC_integral_scale
               _ (a-eta) a
               (CRinv R eta (inr etaPos))
               (fun (eps : CRcarrier R) (_ : 0 < eps) => eps)).
    rewrite (UC_integral_plus _ _ (a-eta) a
                              _ _ _ UC_x (UC_constant (eta-a)) _ _ H).
    rewrite (UC_integral_scale
               _ b (b+eta) _
               (fun eps epsPos => eps)).
    rewrite (UC_integral_plus _ _ b (b+eta)
                              _ _ _ UC_x (UC_constant (-b -eta)) _ _ H1).
    rewrite (UC_integral_constant _ a b 1).
    2: intros; reflexivity. rewrite CRmult_1_r.
    rewrite x_RiemannInt.
    rewrite (UC_integral_constant _ (a-eta) a (eta-a)).
    rewrite x_RiemannInt.
    rewrite (UC_integral_constant _ b (b+eta) (-b-eta)).
    unfold CRminus. rewrite (CRplus_assoc eta).
    rewrite CRplus_comm, CRplus_assoc, (CRplus_comm eta (b+-a)).
    apply CRplus_morph. reflexivity. rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r.
    rewrite <- CRmult_plus_distr_l.
    apply (CRmult_eq_reg_l eta). right. exact etaPos.
    rewrite <- CRmult_assoc, CRinv_r, CRmult_1_l.
    setoid_replace (b + eta + - b) with eta.
    setoid_replace (a + - (a + - eta)) with eta.
    rewrite CRopp_plus_distr. rewrite (CRopp_mult_distr_r eta).
    rewrite CRopp_plus_distr, CRopp_involutive, CRopp_involutive.
    rewrite CRopp_mult_distr_l, CRopp_plus_distr, CRopp_involutive.
    setoid_replace (a * a + - ((a + - eta) * (a + - eta)))
      with (CR_of_Q R 2*a*eta - eta*eta).
    setoid_replace (- ((b + eta) * (b + eta)) + b * b)
      with (-CR_of_Q R 2*b*eta - eta*eta).
    setoid_replace ((- CR_of_Q R 2 * b * eta - eta * eta) * CR_of_Q R (1 # 2))
      with (- eta*eta *CR_of_Q R (1#2) + -(eta*b)).
    setoid_replace ((CR_of_Q R 2 * a * eta - eta * eta) * CR_of_Q R (1 # 2))
      with ( - eta*eta *CR_of_Q R (1#2) + eta*a).
    do 2 rewrite CRplus_assoc. rewrite CRmult_plus_distr_l.
    do 2 rewrite <- (CRplus_assoc (-(eta*b))). rewrite CRplus_opp_l, CRplus_0_l.
    rewrite (CRplus_comm (eta) (-a)), CRmult_plus_distr_l.
    rewrite CRplus_assoc, <- (CRplus_assoc (eta*a)).
    rewrite <- (CRopp_mult_distr_r eta a), CRplus_opp_r, CRplus_0_l.
    rewrite (CRplus_comm (eta*eta)), <- CRplus_assoc, <- CRplus_assoc.
    rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus, Qinv_plus_distr.
    setoid_replace (1+1#2)%Q with 1%Q. 2: reflexivity.
    rewrite CR_of_Q_one, CRmult_1_r, <- CRopp_mult_distr_l.
    rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
    unfold CRminus. rewrite CRmult_comm, CRmult_plus_distr_l.
    rewrite <- CRmult_assoc, <- CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1#2)*2)%Q with 1%Q. rewrite CR_of_Q_one, CRmult_1_l.
    rewrite CRplus_comm, CRmult_comm, CRopp_mult_distr_l, (CRmult_comm a eta).
    reflexivity. reflexivity.
    unfold CRminus. rewrite CRmult_comm, CRmult_plus_distr_l.
    rewrite <- CR_of_Q_opp, <- CRmult_assoc, <- CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace ((1#2)*-(2))%Q with (-(1))%Q.
    rewrite CR_of_Q_opp, CR_of_Q_one, <- CRopp_mult_distr_l, CRmult_1_l.
    rewrite CRplus_comm, CRmult_comm, CRopp_mult_distr_l.
    rewrite (CRopp_mult_distr_r eta b), (CRmult_comm eta (-b)).
    reflexivity. reflexivity.
    rewrite CRmult_plus_distr_l, CRmult_plus_distr_r.
    rewrite CRplus_comm, CRopp_plus_distr, CRopp_plus_distr, <- CRplus_assoc.
    rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite CRmult_plus_distr_r, CRopp_plus_distr, <- CRplus_assoc.
    apply CRplus_morph. 2: reflexivity.
    rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one.
    rewrite <- (CRopp_mult_distr_l), CRmult_plus_distr_r, CRmult_1_l.
    rewrite <- (CRopp_mult_distr_l), CRmult_plus_distr_r.
    rewrite CRopp_plus_distr, (CRmult_comm eta). reflexivity.
    rewrite CRmult_plus_distr_l, CRmult_plus_distr_r.
    rewrite CRopp_plus_distr, CRopp_plus_distr.
    rewrite <- CRplus_assoc, <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite CRmult_plus_distr_r, CRopp_plus_distr.
    rewrite CRopp_mult_distr_l, CRopp_involutive.
    rewrite CRopp_mult_distr_r, CRopp_involutive.
    rewrite CRopp_mult_distr_l, CRopp_involutive, <- CRplus_assoc.
    apply CRplus_morph. rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one.
    rewrite CRmult_plus_distr_r, CRmult_1_l, CRmult_plus_distr_r.
    rewrite (CRmult_comm eta a). reflexivity.
    rewrite CRopp_mult_distr_r. reflexivity.
    rewrite CRopp_plus_distr, CRopp_involutive, <- CRplus_assoc.
    rewrite CRplus_opp_r, CRplus_0_l. reflexivity.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
    intro. reflexivity. intros. reflexivity.
  - intros. unfold CSUCUnitTrapeze. rewrite UCHeavisideIn. unfold UCUnitHeaviside.
    rewrite (CRinv_morph (b + eta - b) eta _ (inr etaPos)).
    rewrite CRmax_right. rewrite CRmin_right.
    apply (CRmult_eq_reg_l eta).
    right. apply etaPos.
    rewrite <- CRmult_assoc, <- CRopp_mult_distr_r, CRinv_r.
    unfold CRminus.
    rewrite (CRmult_plus_distr_l eta), CRmult_1_r.
    rewrite <- CRopp_mult_distr_r, <- CRmult_assoc, CRmult_comm, <- CRmult_assoc.
    rewrite CRinv_l, CRmult_1_l.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l, CRopp_plus_distr, CRopp_plus_distr.
    rewrite CRopp_plus_distr, CRopp_involutive, CRopp_involutive.
    rewrite CRplus_comm, CRplus_assoc. reflexivity.
    apply (CRmult_le_reg_r eta). exact etaPos.
    rewrite CRmult_1_l, CRmult_assoc, CRinv_l, CRmult_1_r.
    apply (CRplus_le_reg_r b).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite CRplus_comm. apply H3.
    apply CRmin_glb. apply CRlt_asym, CRzero_lt_one.
    apply (CRmult_le_reg_r eta). exact etaPos.
    rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r.
    rewrite <- (CRplus_opp_r b). apply CRplus_le_compat_r.
    apply H3. unfold CRminus.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
    apply (CRle_trans _ b _ leab). apply H3.
  - intros. rewrite CSUCTrapezePlateau. reflexivity. exact H3.
  - intros. unfold CSUCUnitTrapeze, UCUnitHeaviside.
    rewrite (CRinv_morph (a - (a- eta)) eta _ (inr etaPos)).
    rewrite (CRinv_morph (b + eta - b) eta _ (inr etaPos)).
    rewrite CRmax_right, CRmin_right.
    rewrite CRmax_left. unfold CRminus. rewrite CRopp_0, CRplus_0_r.
    rewrite CRmult_comm. apply CRmult_morph. reflexivity.
    apply CRplus_morph. reflexivity.
    rewrite CRplus_comm.
    rewrite CRopp_plus_distr, CRopp_involutive. reflexivity.
    apply (CRle_trans _ _ _ (CRmin_r _ _)).
    apply (CRmult_le_reg_r eta). exact etaPos.
    rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r.
    apply (CRplus_le_reg_r b).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite CRplus_0_l.
    apply (CRle_trans _ a). apply H3. exact leab.
    apply (CRmult_le_reg_r eta). exact etaPos.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_1_l.
    apply (CRplus_le_reg_r (a - eta)).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite CRplus_comm. unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    apply H3. apply CRmin_glb. apply CRlt_asym, CRzero_lt_one.
    apply (CRmult_le_reg_r eta). exact etaPos.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_0_l.
    apply (CRplus_le_reg_r (a - eta)).
    unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite CRplus_0_l. unfold CRminus.
    apply H3. unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
    rewrite CRplus_opp_l. apply CRplus_0_l.
    unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
     rewrite CRplus_opp_r, CRopp_involutive. apply CRplus_0_l.
Qed.
