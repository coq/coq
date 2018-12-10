(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The diagonal bijection between nat^2 and nat, as well as convergence
   results for double series. *)

Require Import QArith.
Require Import PeanoNat.
Require Import ArithRing.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.

Local Open Scope ConstructiveReals.


(*********************************************************)
(** * Auxiliary lemmas                                   *)
(*********************************************************)

(* Those lemmas should probably either be inlined,
   or go in other libraries *)

Definition SubSeq : Type
  := { sub : nat -> nat | forall n p:nat, lt n p -> lt (sub n) (sub p) }.

Lemma SubSeqAboveId : forall (un : SubSeq) (n : nat),
    le n (proj1_sig un n).
Proof.
  intros [un inc]. induction n. simpl. apply le_0_n.
  simpl. simpl in IHn. specialize (inc n (S n)).
  unfold lt in inc. apply (le_trans _ (S (un n))).
  apply le_n_S. assumption. apply inc. apply le_refl.
Qed.

(* Inversion of a subsequence *)
Fixpoint SubSeqInv (un : SubSeq) (n p : nat) : nat
  := if Nat.eq_dec (proj1_sig un p) n then p
     else match p with
          | O => S n (* not found *)
          | S k => SubSeqInv un n k
          end.

Lemma SubSeqInvFound : forall (un : SubSeq) (n k : nat),
    (SubSeqInv un n k <= n <-> proj1_sig un (SubSeqInv un n k) = n)%nat.
Proof.
  intros. generalize dependent n. induction k.
  - simpl. split.
    + intro. destruct (Nat.eq_dec (proj1_sig un O) n).
      assumption. exfalso. apply (lt_not_le n (S n)).
      apply le_refl. assumption.
    + intro. destruct (Nat.eq_dec (proj1_sig un O) n). apply le_0_n.
      exfalso. pose proof (SubSeqAboveId un n).
      destruct un. simpl in H. simpl in n0. simpl in H0.
      apply (lt_not_le (x n) (x (S n))). apply l. apply le_refl.
      rewrite H. assumption.
  - split.
    + intro. simpl. simpl in H.
      destruct (Nat.eq_dec (proj1_sig un (S k)) n). assumption.
      apply IHk. assumption.
    + simpl. intro. destruct (Nat.eq_dec (proj1_sig un (S k)) n).
      rewrite <- e. apply SubSeqAboveId. apply IHk. assumption.
Qed.

Lemma SubSeqInvNotFound : forall (un : SubSeq) (n k : nat),
    SubSeqInv un n k = S n
    <-> (forall p:nat, le p k -> proj1_sig un p <> n).
Proof.
  intros. generalize dependent n. induction k.
  - split.
    + intros. intro absurd. simpl in H. destruct (Nat.eq_dec (proj1_sig un O) n).
      discriminate. destruct un. simpl in absurd. simpl in n0.
      inversion H0. subst p. contradiction.
    + intros. simpl. destruct (Nat.eq_dec (proj1_sig un O) n).
      exfalso. exact (H O (le_refl 0) e). reflexivity.
  - split.
    + intros. intro absurd. simpl in H.
      destruct (Nat.eq_dec (proj1_sig un (S k)) n).
      inversion H. subst k. pose proof (SubSeqAboveId un (S n)).
      rewrite e in H1. apply (lt_not_le n (S n)). apply le_refl.
      assumption. apply Nat.le_succ_r in H0. destruct H0.
      specialize (IHk n) as [IHk _].
      specialize (IHk H p H0). contradiction. subst p. contradiction.
    + intros. simpl. destruct (Nat.eq_dec (proj1_sig un (S k)) n).
      exfalso. specialize (H (S k) (le_refl _)). contradiction.
      apply IHk. intros. apply H. apply (le_trans _ k). assumption.
      apply le_S. apply le_refl.
Qed.

Lemma SubSeqInvInit : forall (un : SubSeq) (n : nat),
    SubSeqInv un (proj1_sig un O) n = O.
Proof.
  induction n.
  - simpl. destruct (Nat.eq_dec (proj1_sig un O) (proj1_sig un O)). reflexivity.
    exfalso. exact (n (eq_refl _)).
  - simpl. destruct (Nat.eq_dec (proj1_sig un (S n)) (proj1_sig un O)).
    exfalso. destruct un. simpl in e. apply (lt_not_le (x O) (x (S n))).
    apply l. apply le_n_S. apply le_0_n. rewrite e. apply le_refl.
    apply IHn.
Qed.

(* Realign the indexes, filling with zeros *)
Definition FillSubSeqWithZeros {R : ConstructiveReals}
           (un : nat -> CRcarrier R) (sub : SubSeq) (n : nat) : CRcarrier R
  := if Nat.eq_dec (SubSeqInv sub n n) (S n)
     then 0 else un n.

Lemma sumLastElem : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (n : nat),
    (forall k:nat, lt k n -> un k == 0)
    -> CRsum un n == un n.
Proof.
  intros. destruct n.
  - reflexivity.
  - simpl. rewrite <- (CRplus_0_l (un (S n))). apply CRplus_morph.
    rewrite (CRsum_eq _ (fun n => 0)). rewrite sum_const.
    rewrite CRmult_0_l. reflexivity.
    intros. apply H. apply le_n_S. assumption. apply CRplus_0_l.
Qed.

Lemma FillSubSeqWithZerosInit
  : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (sub : SubSeq),
    CRsum (FillSubSeqWithZeros un sub) (proj1_sig sub O)
    == un (proj1_sig sub O).
Proof.
  intros R un sub.
  replace (un (proj1_sig sub O))
    with ((FillSubSeqWithZeros un sub) (proj1_sig sub O)).
  - apply sumLastElem. intros. unfold FillSubSeqWithZeros.
    destruct (Nat.eq_dec (SubSeqInv sub k k) (S k)). reflexivity.
    exfalso. apply n. clear n. apply SubSeqInvNotFound. intros.
    intro absurd. destruct p. rewrite absurd in H. exact (lt_irrefl k H).
    destruct sub. simpl in absurd, H. apply (lt_not_le (x O) (x (S p))).
    apply l. apply le_n_S. apply le_0_n. rewrite absurd. apply le_S in H.
    apply le_S_n in H. apply H.
  - unfold FillSubSeqWithZeros.
    destruct (Nat.eq_dec (SubSeqInv sub (proj1_sig sub O) (proj1_sig sub O)) (S (proj1_sig sub O))).
    exfalso. pose proof (SubSeqInvNotFound sub (proj1_sig sub O) (proj1_sig sub O)) as [H _].
    specialize (H e O (le_0_n _)). apply H. reflexivity. reflexivity.
Qed.

Lemma FillSubSeqWithZerosStep
  : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (sub : SubSeq) (n : nat),
    CRsum (fun k : nat => FillSubSeqWithZeros un sub (S (proj1_sig sub n) + k))
             (proj1_sig sub (S n) - S (proj1_sig sub n))
    == un (proj1_sig sub (S n)).
Proof.
  intros.
  replace (un (proj1_sig sub (S n)))
    with (FillSubSeqWithZeros un sub (S (proj1_sig sub n)
                                      + (proj1_sig sub (S n) - S (proj1_sig sub n)))).
  - apply (sumLastElem (fun k : nat => FillSubSeqWithZeros un sub (S (proj1_sig sub n) + k))).
    intros. unfold FillSubSeqWithZeros.
    destruct (Nat.eq_dec (SubSeqInv sub (S (proj1_sig sub n) + k) (S (proj1_sig sub n) + k))).
    reflexivity. exfalso. apply n0. clear n0. apply SubSeqInvNotFound. intros.
    intro absurd. (* sub reaches a number between sub n and sub (S n) *)
    destruct sub as [sub inc]. simpl in absurd, H0, H.
    assert (sub p < sub (S n))%nat.
    { rewrite absurd. apply (lt_le_trans _ (S (sub n)
                                            + (sub (S n) - S (sub n)))).
      simpl. apply le_n_S. apply Nat.add_lt_mono_l. assumption. rewrite plus_comm.
      rewrite Nat.sub_add. apply le_refl. apply inc. apply le_refl. }
    destruct (Nat.lt_trichotomy p (S n)).
    apply Nat.le_succ_r in H2. destruct H2.
    specialize (inc p n H2). rewrite absurd in inc.
    apply (lt_not_le (S (sub n + k)) (sub n)). assumption.
    apply le_S. rewrite <- (plus_0_r (sub n)). rewrite <- plus_assoc.
    apply Nat.add_le_mono_l. apply le_0_n. inversion H2. subst p.
    apply (lt_not_le (sub n) (S (sub n + k))). apply le_n_S.
    rewrite <- (plus_0_r (sub n)). rewrite <- plus_assoc.
    apply Nat.add_le_mono_l. apply le_0_n. rewrite <- absurd. apply le_refl.
    destruct H2. subst p. exact (lt_irrefl (sub (S n)) H1).
    specialize (inc (S n) p H2). apply (lt_asym (sub p) (sub (S n))); assumption.
  - rewrite plus_comm. rewrite Nat.sub_add.
    unfold FillSubSeqWithZeros.
    destruct (Nat.eq_dec (SubSeqInv sub (proj1_sig sub (S n)) (proj1_sig sub (S n))) (S (proj1_sig sub (S n)))).
    exfalso. pose proof (SubSeqInvNotFound sub (proj1_sig sub (S n)) (proj1_sig sub (S n))) as [H _].
    specialize (H e (S n) (SubSeqAboveId _ _)). apply H. reflexivity. reflexivity.
    destruct sub. simpl. apply l. apply le_refl.
Qed.

(* The same modulus of convergence applies to any subsequence. *)
Lemma SubSeqCv : forall {R : ConstructiveReals} (un : nat -> CRcarrier R)
                   (sub : SubSeq) (l : CRcarrier R),
    CR_cv R un l -> CR_cv R (fun n => un (proj1_sig sub n)) l.
Proof.
  intros. intros p. specialize (H p) as [N cv].
  exists N. intros. apply cv. apply (le_trans _ i).
  assumption. apply SubSeqAboveId.
Qed.

Lemma SubSeriesCv : forall {R : ConstructiveReals} (un : nat -> CRcarrier R)
                      (sub : SubSeq) (s : CRcarrier R),
    series_cv un s
    -> (forall n:nat, 0 <= un n)
    -> { t : CRcarrier R & series_cv (fun n => un (proj1_sig sub n)) t }.
Proof.
  intros.
  destruct (series_cv_maj (FillSubSeqWithZeros un sub)
                          un s) as [lim [cv _]].
  - intro n. unfold FillSubSeqWithZeros.
    destruct (Nat.eq_dec (SubSeqInv sub n n) (S n)).
    rewrite CRabs_right. apply H0. apply CRle_refl.
    rewrite CRabs_right. apply CRle_refl. apply H0.
  - assumption.
  - exists lim. apply (CR_cv_eq _ (fun n => CRsum (FillSubSeqWithZeros un sub) (proj1_sig sub n))).
    induction n.
    + apply FillSubSeqWithZerosInit.
    + simpl. rewrite <- IHn. clear IHn.
      destruct (Nat.le_exists_sub (S (proj1_sig sub n)) (proj1_sig sub (S n)))
        as [p [inf _]].
      destruct sub. simpl. apply l. apply le_n_S. apply le_refl.
      rewrite inf. rewrite plus_comm. rewrite sum_assoc.
      apply CRplus_morph. reflexivity. rewrite plus_comm. rewrite <- inf.
      apply eq_sym in inf. apply Nat.add_sub_eq_r in inf.
      subst p. apply FillSubSeqWithZerosStep.
    + apply (SubSeqCv _ sub lim cv).
Qed.

(* The points (n,0) are mapped to 0, 1, 3, 6, 10, ... = n(n+1)/2 *)
Definition diagPlane (i j : nat) : nat
  := j + (i+j) * S (i+j)/2.

Definition diagPlaneInvNext i j : prod nat nat
  := match i with
     | O => (* change diag *) pair (S j) O
     | S k => pair k (S j)
     end.

(* Apply n times function f starting at point i j. *)
Fixpoint iterateN2Func (n i j : nat) (f : nat -> nat -> prod nat nat)
  := match n with
     | O => pair i j
     | S p => let (k,l) := iterateN2Func p i j f in f k l
     end.

Definition diagPlaneInv (n : nat) : prod nat nat
  := iterateN2Func n O O diagPlaneInvNext.

Lemma diagPlaneAbsNext : forall n : nat, (S n * (S (S n)) / 2 = n * S n / 2 + S n)%nat.
Proof.
  intro n.
  assert (S n * S (S n) = n * S n + S n * 2)%nat. ring.
  rewrite H. rewrite Nat.div_add. ring.
  intro absurd. inversion absurd.
Qed.

(* g (f ... f 0) = 1 + ... + 1 + g 0 *)
Lemma diagPlaneSurject : forall n : nat, let (i,j) := diagPlaneInv n in
                                  diagPlane i j = n.
Proof.
  assert (forall i j:nat, let (k, l) := diagPlaneInvNext i j in
                   diagPlane k l = S (diagPlane i j)).
  { intros. destruct (diagPlaneInvNext i j) as [k l] eqn:des.
    unfold diagPlane. unfold diagPlaneInvNext in des. destruct i.
    - inversion des. subst l. subst k. clear des.
      rewrite Nat.add_0_l. rewrite Nat.add_0_r. rewrite Nat.add_0_l.
      rewrite diagPlaneAbsNext. ring.
    - inversion des. subst l. subst k. clear des.
      assert ((i + S j) = S i + j)%nat. ring. rewrite H.
      assert (S j + (S i + j) * S (S i + j) / 2
              = S (j + (S i + j) * S (S i + j) / 2))%nat. ring.
      rewrite H0. reflexivity. }

  induction n.
  - reflexivity.
  - unfold diagPlaneInv. simpl. unfold diagPlaneInv in IHn.
    destruct (iterateN2Func n 0 0 diagPlaneInvNext) as [i j].
    rewrite <- IHn. apply H.
Qed.

Lemma diagPlaneInjectBis : forall i j k l : nat,
    diagPlane i j = diagPlane k l -> (i = k /\ j = l).
Proof.
  intros. unfold diagPlane in H. remember (i + j)%nat as I. remember (k + l)%nat as K.
  assert (I = K).
  - destruct (Nat.lt_trichotomy I K).
    + exfalso. unfold lt in H0. assert ((S I) * S (S I) / 2 <= K * S K / 2)%nat.
      apply Nat.div_le_mono. intro absurd. inversion absurd.
      apply Nat.mul_le_mono_nonneg. apply le_0_n. assumption. apply le_0_n.
      apply le_n_S. assumption. rewrite diagPlaneAbsNext in H1.
      apply (Nat.add_le_mono_l (I * S I / 2 + S I) (K * S K / 2) l) in H1.
      rewrite <- H in H1. rewrite <- (Nat.add_comm (S I)) in H1.
      rewrite Nat.add_assoc in H1. apply Nat.le_le_add_le in H1.
      rewrite HeqI in H1. apply (Nat.nle_succ_diag_l j).
      apply (Nat.le_trans (S j) (l + S (i + j))). rewrite <- (Nat.add_0_r (S j)).
      assert (l + S (i + j) = S j + (l + i))%nat. ring. rewrite H2.
      pose proof (Nat.add_le_mono_l). apply Nat.add_le_mono_l. apply le_0_n.
      assumption. apply Nat.le_refl.
    + destruct H0. assumption. exfalso.
      unfold lt in H0. assert ((S K) * S (S K) / 2 <= I * S I / 2)%nat.
      apply Nat.div_le_mono. intro absurd. inversion absurd.
      apply Nat.mul_le_mono_nonneg. apply le_0_n. assumption. apply le_0_n.
      apply le_n_S. assumption. rewrite diagPlaneAbsNext in H1.
      apply (Nat.add_le_mono_l (K * S K / 2 + S K) (I * S I / 2) j) in H1.
      rewrite H in H1. rewrite <- (Nat.add_comm (S K)) in H1.
      rewrite Nat.add_assoc in H1. apply Nat.le_le_add_le in H1.
      rewrite HeqK in H1. apply (Nat.nle_succ_diag_l l).
      apply (Nat.le_trans (S l) (j + S (k + l))). rewrite <- (Nat.add_0_r (S l)).
      assert (j + S (k + l) = S l + (j + k))%nat. ring. rewrite H2.
      pose proof Nat.add_le_mono_l. apply Nat.add_le_mono_l. apply le_0_n.
      assumption. apply Nat.le_refl.
  - rewrite <- H0 in H. apply Nat.add_cancel_r in H. subst l. subst K.
    rewrite H0 in HeqI. apply Nat.add_cancel_r in HeqI. subst k.
    split; reflexivity.
Qed.

Lemma diagPlaneInject : forall i j : nat, diagPlaneInv (diagPlane i j) = pair i j.
Proof.
  intros. destruct (diagPlaneInv (diagPlane i j)) as [k l] eqn:des.
  pose proof (diagPlaneSurject (diagPlane i j)). rewrite des in H.
  apply diagPlaneInjectBis in H. destruct H. subst k. subst l. reflexivity.
Qed.

Definition diagSeq {X : Type} (u : nat -> nat -> X) (p : nat) :=
  let (n, k) := diagPlaneInv p in u n k.

Lemma sub_cancel_m : forall n i:nat, (i <= n ->  n - (n - i) = i)%nat.
Proof.
  intros. pose proof (Nat.sub_add i n H).
  apply Nat.add_sub_eq_l in H0. assumption.
Qed.

Lemma diagSumTriangle : forall {R : ConstructiveReals} (u : nat -> nat -> CRcarrier R),
    forall n : nat, CRsum (diagSeq u) (diagPlane 0 n)
             == CRsum (fun i => CRsum (u i) (n-i)) n.
Proof.
  induction n.
  - simpl. unfold diagSeq. reflexivity.
  - (* The bigger triangle is the smaller one plus the diagonal *)
    assert (forall i:nat, i <= S n -> diagPlane 0 n + S i = diagPlane (S n - i) i)%nat.
    { intros. unfold diagPlane. rewrite plus_0_l. rewrite Nat.sub_add.
      rewrite diagPlaneAbsNext. ring. assumption. }
    pose proof (H (S n)). rewrite Nat.sub_diag in H0. rewrite <- H0.
    assert (diagPlane 0 n + S (S n) = S (diagPlane 0 n) + (S n))%nat. ring.
    rewrite H1. rewrite sum_assoc. rewrite IHn. clear IHn.
    rewrite (reverse_sum (fun k : nat => diagSeq u (S (diagPlane 0 n) + k))).
    simpl.
    (* Remove point S n, 0 *)
    rewrite Nat.sub_diag. rewrite Nat.add_0_r. simpl.
    assert (diagSeq u (S (diagPlane 0 n)) = u (S n) O).
    { pose proof (H O (le_0_n (S n))). rewrite Nat.sub_0_r in H2.
      rewrite Nat.add_succ_r in H2. rewrite Nat.add_0_r in H2.
      rewrite H2. unfold diagSeq. rewrite diagPlaneInject.
      reflexivity. }
    rewrite H2. rewrite <- CRplus_assoc. apply CRplus_morph.
    (* Then rearrange main sum *)
    rewrite <- sum_plus. apply CRsum_eq. intros.
    assert (match i with | 0 => S n | S l => n - l end = S (n - i))%nat.
    { destruct i. rewrite Nat.sub_0_r. reflexivity.
      rewrite Nat.sub_succ_r. rewrite Nat.succ_pred. reflexivity.
      apply Nat.sub_gt. assumption. }
    rewrite H4. simpl.
    apply CRplus_morph. reflexivity.
    pose proof (H (S (n - i))). simpl in H5.
    assert (S (n - i) <= S n)%nat.
    { apply le_n_S. apply Nat.le_sub_l. }
    2: reflexivity. 2: apply le_refl.
    specialize (H5 H6).
    rewrite Nat.add_succ_r in H5. rewrite H5.
    unfold diagSeq. rewrite diagPlaneInject. rewrite sub_cancel_m.
    reflexivity. assumption.
Qed.

Lemma diagSumMajTriangle : forall {R : ConstructiveReals} (u : nat -> nat -> CRcarrier R),
    (forall n k : nat, 0 <= u n k)
    -> forall n : nat, CRsum (diagSeq u) (diagPlane 0 n)
               <= CRsum (fun i => CRsum (u i) n) n.
Proof.
  (* The triangle is included in the square *)
  intros. rewrite diagSumTriangle. apply sum_Rle. intros.
  apply pos_sum_more. intros. apply H. apply Nat.le_sub_l.
Qed.

Lemma diagSumMaj : forall {R : ConstructiveReals} (u : nat -> nat -> CRcarrier R) (A : CRcarrier R),
    (forall n k : nat, 0 <= u n k)
    -> (forall n k : nat, CRsum (fun i => CRsum (u i) k) n <= A)
    -> forall n:nat, CRsum (diagSeq u) n <= A.
Proof.
  (* Finish the triangle and apply previous lemma *)
  intros. destruct (diagPlaneInv n) as [i j] eqn:desN.
  apply (CRle_trans _ (CRsum (diagSeq u) (n+i))).
  - apply pos_sum_more. unfold diagSeq. intros. destruct (diagPlaneInv k).
    apply H. rewrite <- (plus_0_r n). rewrite <- plus_assoc.
    apply Nat.add_le_mono_l. rewrite plus_0_l. apply le_0_n.
  - assert (diagPlane 0 (i+j) = n + i)%nat.
    pose proof (diagPlaneSurject n). rewrite desN in H1.
    unfold diagPlane in H1. unfold diagPlane. rewrite <- H1.
    simpl. ring. rewrite <- H1.
    apply (CRle_trans _ (CRsum (fun k => CRsum (u k) (i+j)) (i+j))).
    apply diagSumMajTriangle. apply H. apply H0.
Qed.

Lemma diagSumMajByLine : forall {R : ConstructiveReals} (u : nat -> nat -> CRcarrier R) (A : CRcarrier R),
    (forall n k : nat, 0 <= u n k)
    -> (forall n:nat, CRsum (diagSeq u) n <= A)
    -> forall n k:nat, CRsum (u n) k <= A.
Proof.
  intros. specialize (H0 (diagPlane 0 (n + k))). rewrite diagSumTriangle in H0.
  apply (CRle_trans _ (CRsum (fun i : nat => CRsum (u i) (n + k - i)) (n + k))).
  pose proof (selectOneInSum (fun i : nat => CRsum (u i) (n + k - i)) (n + k) n).
  simpl in H1. rewrite plus_comm in H1. rewrite Nat.add_sub in H1.
  rewrite plus_comm in H1. apply H1. rewrite <- (plus_0_r n). rewrite <- plus_assoc.
  apply Nat.add_le_mono_l. apply le_0_n. intros. apply cond_pos_sum. intros.
  apply H. assumption.
Qed.

Lemma powerPositive : forall {R : ConstructiveReals} (n:nat),
    (0 < CRpow (CR_of_Q R 2) n).
Proof.
  intros. apply pow_lt. simpl. rewrite <- CR_of_Q_zero.
  apply CR_of_Q_lt. reflexivity.
Qed.

Lemma DiagTriangleShift : forall (p n : nat),
    let (i, j) := diagPlaneInv p in
    le (i + j) n -> le p (diagPlane 0 n).
Proof.
  intros. destruct (diagPlaneInv p) as [i j] eqn:des. intros.
  apply (le_trans p (diagPlane 0 (i+j))).
  replace (diagPlane 0 (i + j)) with (p + i)%nat.
  rewrite <- (plus_0_r p). rewrite <- plus_assoc. apply Nat.add_le_mono_l.
  apply le_0_n. pose proof (diagPlaneSurject p).
  rewrite des in H0. unfold diagPlane in H0. unfold diagPlane.
  subst p. rewrite plus_0_l. ring. unfold diagPlane. rewrite plus_0_l.
  rewrite plus_0_l. remember (i + j)%nat. apply Nat.add_le_mono. assumption.
  apply Nat.div_le_mono. auto. apply Nat.mul_le_mono_nonneg.
  apply le_0_n. assumption. apply le_0_n. apply le_n_S. assumption.
Qed.

Fixpoint DiagTruncateRect {R : ConstructiveReals} (u : nat -> nat -> CRcarrier R)
         (sumCol : nat -> CRcarrier R)
         (eps : CRcarrier R)
         (n : nat)
  : 0 < eps
    -> (forall n:nat, series_cv (u n) (sumCol n))
    -> { p : nat & forall q k:nat,
          le k n -> le p q -> CRabs _ (CRsum (u k) q - sumCol k)
                          < eps * CRpow (CR_of_Q _ (1#2)) k }.
Proof.
  intros.
  destruct n.
  - destruct (CRup_nat (CRinv R eps (inr H))) as [epsN maj].
    specialize (H0 O (Pos.of_nat epsN)) as [p lim]. exists p. intros.
    apply CRltEpsilon. inversion H0.
    subst k. simpl. apply CRltForget. rewrite CRmult_1_r.
    apply (CRle_lt_trans _ (CR_of_Q R (1 # Pos.of_nat epsN))).
    apply lim, H1.
    apply (CRmult_lt_compat_l eps) in maj. 2: exact H.
    rewrite CRinv_r in maj.
    apply (CRmult_lt_reg_l (CR_of_Q R (Z.pos (Pos.of_nat epsN) # 1))).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    rewrite <- CR_of_Q_mult.
    setoid_replace ((Z.pos (Pos.of_nat epsN) # 1) * (1 # Pos.of_nat epsN))%Q with 1%Q.
    rewrite CRmult_comm. rewrite CR_of_Q_one.
    apply (CRlt_le_trans _ _ _ maj).
    apply CRmult_le_compat_l_half. exact H.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. destruct epsN. discriminate.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite SuccNat2Pos.id_succ, Nat2Pos.id. apply le_refl. discriminate.
    unfold Qmult, Qeq, Qnum, Qden. do 2 rewrite Z.mul_1_r. reflexivity.
  - destruct (DiagTruncateRect _ u sumCol eps n H H0) as [pp geo].
    assert (0 < CRpow (CR_of_Q R (1#2)) (S n)).
    { apply pow_lt. simpl. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. }
    destruct (CRup_nat (CRinv R eps (inr H) * (CRinv R (CRpow (CR_of_Q R (1#2)) (S n))) (inr H1)))
      as [epsN maj].
    specialize (H0 (S n) (Pos.of_nat epsN)) as [p lim].
    exists (p + pp)%nat. intros. apply Nat.le_succ_r in H0.
    apply CRltEpsilon. destruct H0.
    + apply CRltForget. apply geo. assumption. apply (le_trans pp (p + pp)).
      rewrite <- (plus_0_l pp). rewrite plus_assoc. apply Nat.add_le_mono_r.
      apply le_0_n. assumption.
    + subst k. apply CRltForget.
      apply (CRle_lt_trans _ (CR_of_Q R (1 # Pos.of_nat epsN))).
      apply lim. apply (le_trans p (p + pp)).
      rewrite <- (plus_0_r p). rewrite <- plus_assoc. apply Nat.add_le_mono_l.
      apply le_0_n. assumption.
      apply (CRmult_lt_compat_l eps) in maj. 2: exact H.
      rewrite <- CRmult_assoc, CRinv_r, CRmult_1_l in maj.
      apply (CRmult_lt_compat_l (CRpow (CR_of_Q R (1 # 2)) (S n))) in maj.
      2: apply pow_lt; rewrite <- CR_of_Q_zero; apply CR_of_Q_lt; reflexivity.
      rewrite CRinv_r in maj.
      apply (CRmult_lt_reg_l (CR_of_Q R (Z.pos (Pos.of_nat epsN) # 1))).
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      rewrite <- CR_of_Q_mult.
      setoid_replace ((Z.pos (Pos.of_nat epsN) # 1) * (1 # Pos.of_nat epsN))%Q with 1%Q.
      rewrite CR_of_Q_one. apply (CRlt_le_trans _ _ _ maj).
      rewrite CRmult_comm. rewrite <- CRmult_assoc.
      apply CRmult_le_compat_r. apply CRlt_asym, pow_lt.
      simpl. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt.
      reflexivity. rewrite CRmult_comm. apply CRmult_le_compat_r.
      apply CRlt_asym, H.
      apply CR_of_Q_le. unfold Qle, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. destruct epsN. discriminate.
      apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
      rewrite SuccNat2Pos.id_succ, Nat2Pos.id. apply le_refl. discriminate.
      unfold Qmult, Qeq, Qnum, Qden. do 2 rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma DiagSeqNegTriangle
  : forall {R : ConstructiveReals} (u : nat -> nat -> CRcarrier R)
      (n p : nat) (eps sAbs : CRcarrier R),
    (forall k : nat,
        le (diagPlane 0 n) k ->
        (CRabs _ (CRsum (diagSeq (fun i j : nat => CRabs _ (u i j))) k - sAbs) < eps ))
    -> CRabs _ (CRsum (fun k : nat => CRsum (u (S n + k)%nat) (p - k)) p) < eps * CR_of_Q R 2.
Proof.
  intros.
  apply (CRle_lt_trans
           _ (CRsum (fun k : nat => CRabs _ (CRsum (u (S n + k)%nat) (p - k))) p)).
  apply multiTriangleIneg.
  apply (CRle_lt_trans
           _ (CRsum (fun k : nat => CRsum (fun l => CRabs _ (u (S n + k)%nat l)) (p - k)) p)).
  apply sum_Rle. intros. apply multiTriangleIneg.
  apply (CRle_lt_trans
           _ (CRsum (diagSeq (fun i j : nat => CRabs _ (u i j))) (diagPlane 0 (S n + p))
              - CRsum (diagSeq (fun i j : nat => CRabs _ (u i j))) (diagPlane 0 n))).
  rewrite (diagSumTriangle _ (S n + p)). rewrite (diagSumTriangle _ n).
  rewrite sum_assoc. rewrite CRplus_comm.
  rewrite <- (CRplus_0_r (CRsum
     (fun k : nat => CRsum (fun l : nat => CRabs _ (u (S n + k)%nat l)) (p - k)) p)).
  setoid_replace (CRsum (fun k : nat => CRsum (fun j : nat => CRabs _ (u (S n + k)%nat j))
                                             (S n + p - (S n + k))) p)
    with (CRsum (fun k : nat => CRsum (fun l : nat => CRabs _ (u (S n + k)%nat l)) (p - k)) p).
  unfold CRminus. rewrite CRplus_assoc. apply CRplus_le_compat_l.
  rewrite CRplus_comm.
  rewrite <- (CRplus_opp_l (CRsum (fun i : nat => CRsum (fun j : nat => CRabs _ (u i j)) (n - i)) n)).
  apply CRplus_le_compat_l.
  apply sum_Rle. intros. apply pos_sum_more. intros. apply CRabs_pos.
  apply Nat.sub_le_mono_r. simpl. apply le_S.
  rewrite <- (plus_0_r n). rewrite <- plus_assoc.
  apply Nat.add_le_mono_l. apply le_0_n. apply CRsum_eq. intros.
  replace (S n + p - (S n + i))%nat with (p - i)%nat. reflexivity. simpl.
  rewrite Nat.sub_add_distr. rewrite plus_comm. rewrite Nat.add_sub. reflexivity.
  apply (CRle_lt_trans _ _ _ (CRle_abs _)).
  setoid_replace
    (CRsum (diagSeq (fun i j : nat => CRabs _ (u i j))) (diagPlane 0 (S n + p)) -
     CRsum (diagSeq (fun i j : nat => CRabs _ (u i j))) (diagPlane 0 n))
    with
      (CRsum (diagSeq (fun i j : nat => CRabs _ (u i j))) (diagPlane 0 (S n + p)) - sAbs
       + (sAbs - CRsum (diagSeq (fun i j : nat => CRabs _ (u i j))) (diagPlane 0 n))).
  apply (CRle_lt_trans _ _ _ (CRabs_triang _ _)).
  rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_l, CRmult_1_r.
  apply CRplus_le_lt_compat. apply CRlt_asym.
  apply (H (diagPlane 0 (S n + p))).
  unfold diagPlane. rewrite plus_0_l. rewrite plus_0_l.
  remember (S n + p)%nat as n0. assert (n <= n0)%nat.
  subst n0. simpl. apply le_S. rewrite <- (plus_0_r n). rewrite <- plus_assoc.
  apply Nat.add_le_mono_l. apply le_0_n.
  apply plus_le_compat. assumption. apply Nat.div_le_mono. auto.
  apply mult_le_compat. assumption. apply le_n_S. assumption.
  rewrite CRabs_minus_sym. apply H. apply le_refl.
  unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.

Lemma DiagSeqInfiniteSum
  : forall {R : ConstructiveReals} (u : nat -> nat -> CRcarrier R)
      (sumCol : nat -> CRcarrier R)
      (sAbs : CRcarrier R),
    series_cv (diagSeq (fun i j => CRabs _ (u i j))) sAbs
    -> (forall n:nat, series_cv (u n) (sumCol n))
    -> { s : CRcarrier R & (series_cv sumCol s)
                    * (series_cv (diagSeq u) s)
                    * (s <= sAbs) }%type.
Proof.
  intros R u sumCol sAbs H7 H1.
  assert { s : CRcarrier R & prod (series_cv (diagSeq u) s) (s <= sAbs) } as [s H].
  { destruct (series_cv_maj (diagSeq u)
                            (diagSeq (fun i j => CRabs _ (u i j)))
                            sAbs) as [s scv].
    intros. unfold diagSeq. destruct (diagPlaneInv n).
    apply CRle_refl. exact H7.
    exists s. exact scv. }
  exists s. split. split. 2: apply H. 2: apply H. destruct H as [H _].
  pose proof (Un_cv_nat_real _ _ H7) as H0. clear H7.
  apply Un_cv_real_nat. intros eps epsPos.
  (* Take big triangle absolute-close to epsilon *)
  assert (forall n : nat, (0 <= diagSeq (fun i j : nat => CRabs _ (u i j)) n)) as diagPos.
  { intro n. unfold diagSeq. destruct (diagPlaneInv n). apply CRabs_pos. }
  assert (0 < eps * CRpow (CR_of_Q R (1#2)) 3) as eighthEpsPos.
  { apply CRmult_lt_0_compat. assumption. apply pow_lt.
    simpl. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. }
  destruct (H0 (eps * CRpow (CR_of_Q R (1#2)) 3) eighthEpsPos) as [Nabs H2].
  pose proof (DiagTriangleShift Nabs) as tShift.
  destruct (diagPlaneInv Nabs) as [i j] eqn:desNabs.
  exists (i + j)%nat. intros n nMaj. specialize (tShift n nMaj).
  setoid_replace eps with (INR 7 * eps * CRpow (CR_of_Q R (1#2)) 3 + eps * CRpow (CR_of_Q R (1#2)) 3).
  setoid_replace (CRsum sumCol n - s)
    with (CRsum sumCol n -CRsum (diagSeq u) (diagPlane 0 n)
         + (CRsum (diagSeq u) (diagPlane 0 n) - s)).
  apply (CRle_lt_trans _ _ _ (CRabs_triang _ _)).
  apply CRplus_le_lt_compat.
  - (* Replace infinite rectangle by finite trapeze, which contains the main triangle. *)
    apply CRlt_asym.
    destruct (DiagTruncateRect u sumCol (eps * CRpow (CR_of_Q R (1#2)) 4) n) as [p geo].
    apply CRmult_lt_0_compat. assumption. apply pow_lt.
    simpl. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    intros. apply H1.
    setoid_replace (CRsum sumCol n - CRsum (diagSeq u) (diagPlane 0 n))
      with (CRsum sumCol n - CRsum (fun k => (CRsum (u k) (p+(n-k)))) n
            + (CRsum (fun k => (CRsum (u k) (p+(n-k)))) n
               - CRsum (diagSeq u) (diagPlane 0 n))).
    apply (CRle_lt_trans _ _ _ (CRabs_triang _ _)).
    setoid_replace (INR 7 * eps * CRpow (CR_of_Q R (1 # 2)) 3)
      with (eps * CRpow (CR_of_Q R (1 # 2)) 3 + INR 6 * eps * CRpow (CR_of_Q R (1 # 2)) 3).
    apply CRplus_le_lt_compat.
    + apply CRlt_asym.
      unfold CRminus.
      rewrite <- sum_opp, <- sum_plus.
      (* Majorate by the trapeze, which contains the triangle *)
      apply (CRle_lt_trans
               _ (CRsum (fun l : nat => CRabs _ (sumCol l - CRsum (u l) (p+(n-l)))) n)).
      apply multiTriangleIneg.
      apply (CRle_lt_trans
               _ (CRsum (fun k => eps * CRpow (CR_of_Q R (1 # 2)) 4 * CRpow (CR_of_Q R (1 # 2)) k) n)).
      apply sum_Rle. intros. specialize (geo (p + (n - k))%nat k).
      apply CRlt_asym.
      rewrite CRabs_minus_sym. apply geo. exact H3.
      rewrite <- (plus_0_r p). rewrite <- plus_assoc. apply Nat.add_le_mono_l.
      apply le_0_n.
      rewrite <- (CRsum_eq (fun k : nat => CRpow (CR_of_Q R (1 # 2)) k * (eps * CRpow (CR_of_Q R (1 # 2)) 4))).
      rewrite sum_scale. rewrite CRmult_comm, CRmult_assoc.
      apply CRmult_lt_compat_l. assumption.
      setoid_replace (CRpow (CR_of_Q R (1 # 2)) 3)
        with (CRpow (CR_of_Q R (1 # 2)) 4 * CR_of_Q R 2).
      apply CRmult_lt_compat_l. apply pow_lt. simpl.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      apply GeoHalfBelowTwo.
      setoid_replace (CRpow (CR_of_Q R (1 # 2)) 4)
        with (CR_of_Q R (1#2) * CRpow (CR_of_Q R (1 # 2)) 3). 2: reflexivity.
      rewrite CRmult_comm, <- CRmult_assoc, <- (CR_of_Q_mult _ 2).
      setoid_replace (2 * (1 # 2))%Q with 1%Q. rewrite CR_of_Q_one, CRmult_1_l.
      reflexivity. reflexivity.
      intros. apply CRmult_comm.
    + destruct p.
      setoid_replace (CRsum (fun k : nat => CRsum (u k) (0 + (n - k))) n)
        with (CRsum (diagSeq u) (diagPlane 0 n)).
      unfold CRminus.
      rewrite CRplus_opp_r. rewrite CRabs_right. 2: apply CRle_refl.
      apply CRmult_lt_0_compat. apply CRmult_lt_0_compat.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      assumption. apply pow_lt. simpl. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_lt. reflexivity.
      simpl. rewrite diagSumTriangle. reflexivity.
      setoid_replace (CRsum (fun k : nat => CRsum (u k) (S p + (n - k))) n)
        with (CRsum (diagSeq u) (diagPlane 0 (S n+p))
              - CRsum (fun k : nat => CRsum (u (S n + k)%nat) (p - k)) p).
      unfold CRminus. rewrite CRplus_comm. rewrite <- CRplus_assoc.
      setoid_replace (- CRsum (diagSeq u) (diagPlane 0 n) +
        CRsum (diagSeq u) (diagPlane 0 (S n + p)) +
        - CRsum (fun k : nat => CRsum (u (S n + k)%nat) (p - k)) p)
        with (CRsum (diagSeq u) (diagPlane 0 (S n + p))
              - CRsum (diagSeq u) (diagPlane 0 n)
                - (CRsum (fun k : nat => CRsum (u (S n + k)%nat) (p - k)) p)).
      apply (CRle_lt_trans _ _ _ (CRabs_triang _ _)).
      rewrite CRabs_opp.
      setoid_replace (INR 6 * eps * CRpow (CR_of_Q R (1 # 2)) 3)
        with (INR 2 * eps * CRpow (CR_of_Q R (1 # 2)) 3 + INR 4 * eps * CRpow (CR_of_Q R (1 # 2)) 3).
      apply CRplus_le_lt_compat.
      setoid_replace (CRsum (diagSeq u) (diagPlane 0 (S n + p))
                      - CRsum (diagSeq u) (diagPlane 0 n))
        with (CRsum (diagSeq u) (diagPlane 0 (S n + p)) - s
              + (s - CRsum (diagSeq u) (diagPlane 0 n))).
      apply (CRle_trans _ _ _ (CRabs_triang _ _)).
      unfold INR. simpl (Z.of_nat 2 # 1).
      rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_plus_distr_r, CRmult_1_l.
      rewrite CRmult_plus_distr_r.
      apply CRplus_le_compat.
      apply (CRle_trans _ (sAbs - CRsum (fun n0 : nat => CRabs _ (diagSeq u n0))
                                           (diagPlane 0 (S n + p)))).
      apply (series_cv_abs_remainder (diagSeq u)).
      apply H.
      apply (series_cv_eq (diagSeq (fun i j : nat => CRabs _ (u i j)))).
      intros. unfold diagSeq. destruct (diagPlaneInv n0). reflexivity.
      apply Un_cv_real_nat. apply H0.
      rewrite <- (CRsum_eq (diagSeq (fun i j : nat => CRabs _ (u i j)))).
      apply CRlt_asym.
      apply (CRle_lt_trans _ _ _ (CRle_abs _)).
      rewrite CRabs_minus_sym.
      apply H2. pose proof (DiagTriangleShift Nabs (S n +p)). rewrite desNabs in H3.
      apply H3. apply (le_trans _ n). assumption. simpl. apply le_S.
      rewrite <- (plus_0_r n). rewrite <- plus_assoc.
      apply Nat.add_le_mono_l. apply le_0_n.
      intros. unfold diagSeq. destruct (diagPlaneInv i0). reflexivity.
      rewrite CRabs_minus_sym.
      apply (CRle_trans _ (sAbs - CRsum (fun n0 : nat => CRabs _ (diagSeq u n0))
                                           (diagPlane 0 n))).
      apply (series_cv_abs_remainder
               (fun n0 : nat => diagSeq u n0)).
      assumption.
      apply (series_cv_eq (diagSeq (fun i j : nat => CRabs _ (u i j)))).
      intros. unfold diagSeq. destruct (diagPlaneInv n0). reflexivity.
      apply Un_cv_real_nat. apply H0.
      rewrite <- (CRsum_eq (diagSeq (fun i j : nat => CRabs _ (u i j)))).
      apply CRlt_asym.
      apply (CRle_lt_trans _ _ _ (CRle_abs _)).
      rewrite CRabs_minus_sym.
      apply H2. assumption. intros. unfold diagSeq. destruct (diagPlaneInv i0).
      reflexivity.
      unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
      reflexivity. rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
      apply (CRlt_trans _ (eps * CRpow (CR_of_Q R (1 # 2)) 3 * CR_of_Q R 2)).
      apply (DiagSeqNegTriangle _ _ _ _ sAbs). intros. apply H2.
      apply (le_trans _ (diagPlane 0 n)); assumption. rewrite <- (CRmult_comm (CR_of_Q R 2)).
      rewrite CRmult_assoc. apply CRmult_lt_compat_r. apply CRmult_lt_0_compat.
      assumption. apply pow_lt. simpl.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      apply CR_of_Q_lt. reflexivity.
      setoid_replace (@INR R 6) with (@INR R 2 + @INR R 4).
      do 2 rewrite CRmult_plus_distr_r. reflexivity.
      unfold INR. rewrite <- CR_of_Q_plus. apply CR_of_Q_morph.
      rewrite Qinv_plus_distr. reflexivity.
      apply CRplus_morph. 2: reflexivity.
      rewrite (diagSumTriangle _ (S n + p)). unfold CRminus.
      rewrite CRplus_comm. reflexivity.
      rewrite (diagSumTriangle _ (S n + p)). unfold CRminus.
      rewrite sum_assoc.
      rewrite (CRsum_eq (fun k : nat => CRsum (u (S n + k)%nat) (S n + p - (S n + k)))
                        (fun k : nat => CRsum (u (S n + k)%nat) (p - k))).
      unfold CRminus. rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
      apply CRsum_eq. intros. replace (S n + p - i0)%nat with (S p + (n - i0))%nat.
      reflexivity. rewrite Nat.add_sub_assoc. simpl. destruct i0.
      rewrite plus_comm. reflexivity. rewrite plus_comm. reflexivity. assumption.
      intros. replace (S n + p - (S n + i0))%nat with (p - i0)%nat. reflexivity.
      simpl. rewrite Nat.sub_add_distr. rewrite plus_comm. rewrite Nat.add_sub.
      reflexivity.
    + setoid_replace (@INR R 7) with (1 + @INR R 6).
      do 2 rewrite CRmult_plus_distr_r. rewrite CRmult_1_l. reflexivity.
      unfold INR. rewrite <- CR_of_Q_one, <- CR_of_Q_plus. apply CR_of_Q_morph.
      rewrite Qinv_plus_distr. reflexivity.
    + unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
      reflexivity. rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
  - apply (CRle_lt_trans _ (sAbs - CRsum (fun n => CRabs _ (diagSeq u n))
                                            (diagPlane 0 n))).
    apply (series_cv_abs_remainder
             (fun n0 : nat => diagSeq u n0)).
    apply H.
    apply (series_cv_eq (diagSeq (fun i j : nat => CRabs _ (u i j)))).
    intros. unfold diagSeq. destruct (diagPlaneInv n0). reflexivity.
    apply Un_cv_real_nat. apply H0.
    rewrite <- (CRsum_eq (diagSeq (fun i j : nat => CRabs _ (u i j)))).
    apply (CRle_lt_trans _ _ _ (CRle_abs _)).
    rewrite CRabs_minus_sym.
    apply H2. assumption.
    intros. unfold diagSeq. destruct (diagPlaneInv i0). reflexivity.
  - unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
    reflexivity. rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
  - setoid_replace (CRpow (CR_of_Q R (1 # 2)) 3) with (CR_of_Q R (1 # 8)).
    rewrite <- CRmult_plus_distr_r.
    setoid_replace (INR 7 * eps + eps) with (eps * INR 8).
    rewrite CRmult_assoc. unfold INR. rewrite <- CR_of_Q_mult.
    setoid_replace ((Z.of_nat 8 # 1) * (1 # 8))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_r. reflexivity. reflexivity.
    setoid_replace (@INR R 8) with (1 + @INR R 7).
    rewrite CRmult_plus_distr_l, CRmult_1_r, CRplus_comm, CRmult_comm. reflexivity.
    unfold INR. rewrite <- CR_of_Q_one, <- CR_of_Q_plus.
    apply CR_of_Q_morph. reflexivity.
    unfold CRpow. rewrite CRmult_1_r.
    do 2 rewrite <- CR_of_Q_mult. apply CR_of_Q_morph. reflexivity.
Qed.

Lemma growing_transit : forall {R : ConstructiveReals} (un : nat -> CRcarrier R),
    (forall n:nat, un n <= un (S n))
    -> forall n p : nat, le n p -> un n <= un p.
Proof.
  induction p.
  - intros. inversion H0. apply CRle_refl.
  - intros. apply Nat.le_succ_r in H0. destruct H0.
    apply (CRle_trans _ (un p)). apply IHp, H0. apply H.
    subst n. apply CRle_refl.
Qed.

(* In the positive case, requesting the convergence of Rabs diagSeq
   would be absurd, as it is the same as the conclusion. *)
Lemma DiagSeqInfiniteSumColPos
  : forall {R : ConstructiveReals} (u : nat -> nat -> CRcarrier R)
      (sumCol : nat -> CRcarrier R)
      (s : CRcarrier R),
    (forall n k:nat, 0 <= u n k)
    -> (forall n:nat, series_cv (u n) (sumCol n))
    -> (series_cv sumCol s)
    -> (series_cv (diagSeq u) s).
Proof.
  intros R u sumCol s uPos cvCol cvSumCol.
  assert (forall n:nat, CRsum (diagSeq u) n <= s) as belowS.
  { apply diagSumMaj. assumption. intros n k.
    apply (CRle_trans _ (CRsum sumCol n)). apply sum_Rle.
    intros. apply growing_ineq. 2: apply cvCol.
    intro i. rewrite <- CRplus_0_r. apply CRplus_le_compat.
    apply CRle_refl. apply uPos.
    apply growing_ineq. 2: apply cvSumCol.
    intro i. rewrite <- CRplus_0_r. apply CRplus_le_compat.
    apply CRle_refl.
    apply (series_cv_nonneg (u (S i))). apply uPos.
    apply cvCol. }
  (* Conversely, show that diagSeq approaches s *)
  intros n.
  destruct (cvSumCol (2*n)%positive) as [N H1].
  assert (0 < CR_of_Q R (1 # 4*n)) as quarterEpsPos.
  { rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. }
  destruct (DiagTruncateRect u sumCol (CR_of_Q R (1 # 4*n)) N quarterEpsPos cvCol)
    as [p H2].
  exists (diagPlane 0 (N+p)). intros.
  (* Go back to the N+p triangle *)
  rewrite CRabs_minus_sym. rewrite CRabs_right.
  apply (CRle_trans _ (s - CRsum (diagSeq u) (diagPlane 0 (N + p)))).
  unfold CRminus. apply CRplus_le_compat_l.
  apply CRopp_ge_le_contravar. apply growing_transit.
  - intro k. rewrite <- (CRplus_0_r (CRsum (diagSeq u) k)).
    simpl. apply CRplus_le_compat_l. unfold diagSeq.
    destruct (diagPlaneInv (S k)). apply uPos.
  - apply H.
  - rewrite diagSumTriangle.
    (* Truncate to the N trapeze *)
    apply (CRle_trans _ (s - CRsum (fun i : nat => CRsum (u i) (N + p - i)) N)).
    unfold CRminus. apply CRplus_le_compat_l.
    apply CRopp_ge_le_contravar. apply pos_sum_more.
    intro k. apply cond_pos_sum. apply uPos.
    rewrite <- (plus_0_r N). rewrite <- plus_assoc. apply Nat.add_le_mono_l.
    apply le_0_n.
    (* Extend to the infinite vertical rectangle *)
    apply (CRle_trans _ (s - CRsum sumCol N + CR_of_Q R (1#2*n))).
    specialize (H1 N (le_refl N)).
    rewrite CRabs_minus_sym in H1.
    apply (CRle_trans _ _ _ (CRle_abs _)) in H1.
    unfold CRminus. rewrite CRplus_assoc. apply CRplus_le_compat_l.
    apply (CRplus_le_reg_l (CRsum sumCol N)). rewrite <- CRplus_assoc.
    rewrite CRplus_opp_r. rewrite CRplus_0_l. rewrite <- sum_opp.
    rewrite <- sum_plus.
    apply (CRle_trans
             _ (CRsum (fun k => CR_of_Q R (1#4*n) * CRpow (CR_of_Q R (1#2)) k) N)).
    apply sum_Rle. intros n0 H0. specialize (H2 (N+p-n0)%nat n0).
    apply (CRle_trans _ _ _ (CRle_abs _)).
    pose proof (CRabs_minus_sym (sumCol n0)). unfold CRminus in H3.
    rewrite H3. clear H3. apply CRlt_asym, H2.
    exact H0. rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc. rewrite <- (plus_0_r p).
    rewrite <- plus_assoc. apply Nat.add_le_mono_l. apply le_0_n.
    assumption.
    rewrite (CRsum_eq _ (fun k : nat => CRpow (CR_of_Q R (1#2)) k * (CR_of_Q R (1# 4*n)))).
    rewrite sum_scale, CRmult_comm. apply CRlt_asym.
    apply (CRlt_le_trans _ (CR_of_Q R (1#4*n) * CR_of_Q R 2)).
    apply CRmult_lt_compat_l.
    exact quarterEpsPos. apply GeoHalfBelowTwo.
    rewrite <- CR_of_Q_mult. apply CR_of_Q_le.
    unfold Qmult, Qle, Qnum, Qden. do 2 rewrite Z.mul_1_l.
    rewrite <- Pos2Z.inj_mul. rewrite Pos.mul_1_r, Pos.mul_assoc.
    apply Z.le_refl.
    intros. apply CRmult_comm.
    apply (CRplus_le_reg_r (- CR_of_Q R (1#2*n))).
    rewrite CRplus_assoc.
    rewrite CRplus_opp_r. rewrite CRplus_0_r.
    rewrite <- CR_of_Q_opp, <- CR_of_Q_plus.
    setoid_replace ((1 # n) + - (1 # 2 * n))%Q with (1 # 2*n)%Q.
    specialize (H1 N (le_refl N)).
    apply (CRle_trans _ _ _ (CRle_abs _)).
    rewrite CRabs_minus_sym. apply H1.
    rewrite <- (Qplus_inj_r _ _ (1#2*n)).
    rewrite Qinv_plus_distr. ring_simplify. reflexivity.
  - rewrite <- (CRplus_opp_r (CRsum (diagSeq u) i)).
    apply CRplus_le_compat. apply belowS. apply CRle_refl.
Qed.

Lemma Rlt_0_half : forall {R : ConstructiveReals}, 0 < CR_of_Q R (1#2).
Proof.
  intro R. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
Qed.

Fixpoint FindPointInSubdivision (Pn : nat -> nat) (n : nat)
  : (forall k, Pn k < Pn (S k))%nat
    -> (Pn O = O)
    -> { p : nat | (Pn p <= n < Pn (S p))%nat }.
Proof.
  intros. destruct n.
  - exists O. repeat split. rewrite H0. apply le_refl.
    specialize (H O). rewrite H0 in H. apply H.
  - destruct (FindPointInSubdivision Pn n H H0) as [k kmaj].
    destruct (le_lt_dec (Pn (S k)) (S n)).
    + exists (S k). split. apply l. apply (lt_le_trans _ (S (Pn (S k)))).
      apply le_n_S. apply kmaj. apply (H (S k)).
    + exists k. split. 2: apply l. apply (le_trans _ n).
      apply kmaj. apply le_S. apply le_refl.
Qed.

Lemma FindPointInSubdivisionSmallest
  : forall (Pn : nat -> nat) (Pinc : forall k, lt (Pn k) (Pn (S k)))
      (Pzero : Pn O = O) (n i : nat),
    le (Pn i) n
    -> le i (proj1_sig (FindPointInSubdivision Pn n Pinc Pzero)).
Proof.
  induction i.
  - intros. apply le_0_n.
  - intros. destruct (FindPointInSubdivision Pn n Pinc Pzero) as [r rmaj].
    simpl in IHi. simpl. assert (i <= r)%nat.
    apply IHi. apply (le_trans _ (Pn (S i))). 2: apply H.
    specialize (Pinc i). apply le_S in Pinc. apply le_S_n in Pinc. apply Pinc.
    clear IHi. apply le_n_S in H0. apply Nat.le_succ_r in H0.
    destruct H0. apply H0. exfalso. inversion H0. subst i.
    apply Nat.le_ngt in H. destruct rmaj. contradiction.
Qed.

Lemma ROpenBallConvex : forall {R : ConstructiveReals} (x r a b c : CRcarrier R),
    (a <= b /\ b <= c)
    -> CRabs _ (x - a) <= r
    -> CRabs _ (x - c) <= r
    -> CRabs _ (x - b) <= r.
Proof.
  intros. apply CRabs_le. destruct H.
  apply CRabs_def2 in H0. apply CRabs_def2 in H1. split.
  - apply (CRle_trans _ (x-c)). apply H1.
    apply CRplus_le_compat_l. apply CRopp_ge_le_contravar.
    apply H2.
  - apply (CRle_trans _ (x-a)). 2: apply H0.
    apply CRplus_le_compat_l. apply CRopp_ge_le_contravar.
    apply H.
Qed.


(* Positivity is necessary, because 1 - 1 can be summed
   by blocks of two and make a constant zero sum,
   whereas individually the sum oscillates between 0 and 1. *)
Lemma infinite_sum_assoc
  : forall {R : ConstructiveReals} (xn : nat -> CRcarrier R)
      (Pn : nat -> nat) (s : CRcarrier R),
    (forall n, Pn n < Pn (S n))%nat
    -> (forall n, 0 <= xn n)
    -> Pn O = O
    -> (series_cv (fun n => CRsum (fun k => xn (k+ Pn n)%nat)
                                        (Pn (S n) - Pn n - 1)) s)
    -> series_cv xn s.
Proof.
  intros.
  assert (forall p q : nat, p <= q -> Pn p <= Pn q)%nat as PnInc.
  { induction q.
    - intros. inversion H3. apply le_refl.
    - intros. apply Nat.le_succ_r in H3. destruct H3.
      apply (le_trans _ (Pn q)). apply IHq. apply H3.
      apply (le_trans _ (S (Pn q))). apply le_S. apply le_refl.
      apply H. subst p. apply le_refl. }
  assert (forall p:nat,
             CRsum (fun n : nat => CRsum (fun k : nat => xn (k + Pn n))%nat (Pn (S n) - Pn n - 1)) p
             == CRsum xn (Pn (S p) - 1)) as assocSum.
  { induction p.
    - simpl. repeat rewrite H1. rewrite Nat.sub_0_r.
      rewrite (CRsum_eq _ xn). reflexivity. intros.
      rewrite plus_0_r. reflexivity.
    - simpl. rewrite IHp. clear IHp.
      destruct (Nat.le_exists_sub 1 (Pn (S p))) as [r [H3 _]].
      specialize (H p). apply (le_trans _ (S (Pn p))). 2: apply H.
      apply le_n_S. apply le_0_n.
      assert (r+1 = S r)%nat. rewrite plus_comm. reflexivity.
      rewrite H3. rewrite Nat.add_sub.
      rewrite (CRsum_eq (fun k : nat => xn (k + (r + 1))%nat) (fun k : nat => xn (S r + k)%nat)).
      rewrite <- (sum_assoc xn r).
      replace (S r + (Pn (S (S p)) - (r + 1) - 1))%nat
        with (Pn (S (S p)) - 1)%nat.
      reflexivity. rewrite Nat.add_sub_assoc.
      rewrite <- H4. rewrite plus_comm. rewrite Nat.sub_add.
      reflexivity. rewrite <- H3. apply (le_trans _ (S (Pn (S p)))).
      apply le_S. apply le_refl. apply H. rewrite <- H3.
      destruct (Nat.le_exists_sub (S (Pn (S p))) (Pn (S (S p)))).
      apply H. destruct H5. rewrite H5. simpl.
      replace (S (Pn (S p))) with (1 + Pn (S p))%nat.
      rewrite plus_assoc. rewrite Nat.add_sub. 2: reflexivity.
      rewrite plus_comm. apply le_n_S. apply le_0_n.
      intros. rewrite plus_comm. rewrite (plus_comm r). reflexivity. }
  assert (forall n:nat,
             (Pn 1 <= n)%nat
             -> let (p,_) := FindPointInSubdivision Pn n H H1 in
                (CRsum (fun n : nat => CRsum (fun k : nat => xn (k + Pn n))%nat (Pn (S n) - Pn n - 1)) (p-1)
                 <= CRsum xn n
                 /\ CRsum xn n
                 <= CRsum (fun n : nat => CRsum (fun k : nat => xn (k + Pn n))%nat (Pn (S n) - Pn n - 1)) p)).
  { intro n. destruct (FindPointInSubdivision Pn n H H1) as [p pmaj].
    repeat rewrite assocSum. split.
    apply pos_sum_more. apply H0. destruct p.
    exfalso. apply Nat.le_ngt in H3. destruct pmaj. contradiction.
    simpl. rewrite Nat.sub_0_r. apply (le_trans _ (Pn (S p))).
    2: apply pmaj. apply Nat.le_sub_l.
    apply pos_sum_more. apply H0. apply Nat.le_add_le_sub_r.
    rewrite plus_comm. apply pmaj. }
  intros n. specialize (H2 n) as [p pmaj].
  exists (Pn (S p)). intros. specialize (H3 i).
  pose proof (FindPointInSubdivisionSmallest Pn H H1 i).
  destruct (FindPointInSubdivision Pn i H H1) as [q qmaj].
  rewrite CRabs_minus_sym.
  assert (S p <= q)%nat.
  { apply H4. apply H2. }
  apply (ROpenBallConvex
           _ _ (CRsum (fun n : nat => CRsum (fun k : nat => xn (k + Pn n)%nat) (Pn (S n) - Pn n - 1)) (q-1))
           _ (CRsum (fun n : nat => CRsum (fun k : nat => xn (k + Pn n)%nat) (Pn (S n) - Pn n - 1)) q)).
  split; apply H3.
  apply (le_trans _ (Pn (S p))). 2: apply H2.
  apply PnInc. apply le_n_S. apply le_0_n.
  apply (le_trans _ (Pn (S p))). 2: apply H2.
  apply PnInc. apply le_n_S. apply le_0_n.
  rewrite CRabs_minus_sym.
  apply pmaj. apply Nat.le_add_le_sub_r.
  rewrite plus_comm. apply H5.
  rewrite CRabs_minus_sym; apply pmaj.
  apply (le_trans _ (S p)).
  apply le_S. apply le_refl. apply H5.
Qed.
