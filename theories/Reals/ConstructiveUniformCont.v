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
  The uniformly continuous functions R -> R.
 *)

Require Import List Permutation Orders Sorted Mergesort.
Require Import QArith Qpower.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructiveDiagonal.

Local Open Scope ConstructiveReals.


Definition UniformCont {R : ConstructiveReals}
           (f : CRcarrier R -> CRcarrier R)
           (cont_mod : forall x:CRcarrier R, 0 < x -> CRcarrier R) : Set
  := prod (forall (x:CRcarrier R) (xPos : 0 < x), 0 < cont_mod x xPos) (* otherwise any function is trivially continuous *)
      (forall (eps x y : CRcarrier R) (epsPos : 0 < eps),
           CRabs _ (x - y) < cont_mod eps epsPos
           -> CRabs _ (f x - f y) < eps).

Definition Lipschitz {R : ConstructiveReals}
           (f : CRcarrier R -> CRcarrier R) (k : CRcarrier R) : Set
  := forall (x y : CRcarrier R),
    CRabs _ (f x - f y) <= k * CRabs _ (x - y).

Lemma UniformContProper :
  forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
    (cont_mod : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    UniformCont f cont_mod
    -> (forall x y : CRcarrier R, x == y -> f x == f y).
Proof.
  intros. destruct H. split.
  - intro abs.
    assert (0 < f y - f x) as epsPos.
    { rewrite <- (CRplus_opp_r (f x)).
      apply CRplus_lt_compat_r. exact abs. }
    specialize (c0 (f y - f x) x y epsPos).
    apply (CRle_abs (f y - f x)).
    rewrite CRabs_minus_sym. apply c0.
    apply (CRle_lt_trans _ (CRabs _ 0)).
    rewrite H0. unfold CRminus. rewrite CRplus_opp_r.
    apply CRle_refl. rewrite CRabs_right. apply c.
    apply CRle_refl.
  - intro abs.
    assert (0 < f x - f y) as epsPos.
    { rewrite <- (CRplus_opp_r (f y)).
      apply CRplus_lt_compat_r. exact abs. }
    specialize (c0 (f x - f y) x y epsPos).
    apply (CRle_abs (f x - f y)).
    apply c0. apply (CRle_lt_trans _ (CRabs _ 0)).
    rewrite H0. unfold CRminus. rewrite CRplus_opp_r.
    apply CRle_refl. rewrite CRabs_right. apply c.
    apply CRle_refl.
Qed.

Lemma LipschitzUC
  : forall {R : ConstructiveReals}
      (f : CRcarrier R -> CRcarrier R)
      (k : CRcarrier R) (kPos : 0 < k),
    Lipschitz f k
    -> UniformCont f (fun eps epsPos => eps * CRinv R k (inr kPos)).
Proof.
  split.
  - intros eps epsPos.
    apply (CRle_lt_trans _ (eps * 0)). rewrite CRmult_0_r.
    apply CRle_refl. apply CRmult_lt_compat_l. exact epsPos.
    apply CRinv_0_lt_compat, kPos.
  - intros. apply (CRle_lt_trans _ _ _ (H x y)).
    apply (CRmult_lt_compat_r k) in H0.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r in H0.
    rewrite CRmult_comm. exact H0. exact kPos.
Qed.


(* Compact support and uniformly continuous.
   On R we simplify this by segment support and uniformly continuous. *)
Definition CSUC {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
           (a b : CRcarrier R) (cont_mod : forall x:CRcarrier R, 0 < x -> CRcarrier R) : Set
  := prod (UniformCont f cont_mod)
     (forall x : CRcarrier R, (sum (x < a) (b < x)) -> f x == 0).

Lemma CSUC_connect_support
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (a b : CRcarrier R) (cont_mod : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    CSUC f a b cont_mod
    -> (forall x : CRcarrier R, (sum (x <= a) (b <= x)) -> f x == 0).
Proof.
  intros. destruct H, u. split.
  - intro abs. destruct H0.
    + apply CRopp_gt_lt_contravar in abs. rewrite CRopp_0 in abs.
      specialize (c1 (-f x) (x - (cont_mod (-f x) abs) * CR_of_Q R (1#2)) x abs).
      apply (CRle_abs (-f x)).
      apply (CRle_lt_trans
               _ (CRabs _ (f (x - cont_mod (- f x) abs * CR_of_Q R (1 # 2)) - f x))).
      rewrite (c (x - cont_mod (-f x) abs * CR_of_Q R (1#2))).
      unfold CRminus. rewrite CRplus_0_l. apply CRle_refl.
      left. apply (CRlt_le_trans _ (x + 0)).
      apply CRplus_lt_compat_l. rewrite <- CRopp_0. apply CRopp_gt_lt_contravar.
      apply CRmult_lt_0_compat. apply c0.
      apply CR_of_Q_pos; reflexivity.
      rewrite CRplus_0_r. exact c2. apply c1.
      setoid_replace (x + - (cont_mod (-f x) abs * CR_of_Q R (1#2)) + - x)
        with (- (cont_mod (-f x) abs * CR_of_Q R (1#2))).
      rewrite CRabs_opp. rewrite CRabs_right.
      rewrite <- (CRmult_1_r (cont_mod (- f x) abs)).
      rewrite CRmult_assoc. apply CRmult_lt_compat_l. apply c0.
      rewrite CRmult_1_l. rewrite <- CR_of_Q_one. apply CR_of_Q_lt; reflexivity.
      apply CRlt_asym.
      apply CRmult_lt_0_compat. apply c0.
      apply CR_of_Q_pos; reflexivity.
      rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      reflexivity.
    + apply CRopp_gt_lt_contravar in abs. rewrite CRopp_0 in abs.
      specialize (c1 (-f x) (x + (cont_mod (-f x) abs) * CR_of_Q R (1#2)) x abs).
      apply (CRle_abs (-f x)).
      apply (CRle_lt_trans
               _ (CRabs _ (f (x + cont_mod (- f x) abs * CR_of_Q R (1 # 2)) - f x))).
      rewrite (c (x + cont_mod (-f x) abs * CR_of_Q R (1#2))).
      unfold CRminus. rewrite CRplus_0_l. apply CRle_refl.
      right. apply (CRle_lt_trans _ (x + 0)).
      rewrite CRplus_0_r. exact c2. apply CRplus_lt_compat_l.
      apply CRmult_lt_0_compat. apply c0.
      apply CR_of_Q_pos; reflexivity.
      apply c1.
      setoid_replace (x + (cont_mod (-f x) abs * CR_of_Q R (1#2)) + - x)
        with (cont_mod (-f x) abs * CR_of_Q R (1#2)).
      rewrite CRabs_right. rewrite <- (CRmult_1_r (cont_mod (- f x) abs)).
      rewrite CRmult_assoc. apply CRmult_lt_compat_l. apply c0.
      rewrite CRmult_1_l.
      rewrite <- CR_of_Q_one. apply CR_of_Q_lt; reflexivity.
      apply CRlt_asym.
      apply CRmult_lt_0_compat. apply c0.
      apply CR_of_Q_pos; reflexivity.
      rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      reflexivity.
  - intro abs. destruct H0.
    + specialize (c1 (f x) (x - (cont_mod (f x) abs) * CR_of_Q R (1#2)) x abs).
      apply (CRle_abs (f x)).
      apply (CRle_lt_trans
               _ (CRabs _ (f (x - cont_mod (f x) abs * CR_of_Q R (1 # 2)) - f x))).
      rewrite (c (x - cont_mod (f x) abs * CR_of_Q R (1#2))).
      unfold CRminus. rewrite CRplus_0_l, CRabs_opp.
      apply CRle_refl. left. apply (CRlt_le_trans _ (x + 0)).
      apply CRplus_lt_compat_l. rewrite <- CRopp_0. apply CRopp_gt_lt_contravar.
      apply CRmult_lt_0_compat. apply c0.
      apply CR_of_Q_pos; reflexivity.
      rewrite CRplus_0_r. exact c2. apply c1.
      setoid_replace (x + - (cont_mod (f x) abs * CR_of_Q R (1#2)) + - x)
        with (- (cont_mod (f x) abs * CR_of_Q R (1#2))).
      rewrite CRabs_opp. rewrite CRabs_right.
      rewrite <- (CRmult_1_r (cont_mod (f x) abs)).
      rewrite CRmult_assoc. apply CRmult_lt_compat_l. apply c0.
      rewrite CRmult_1_l. rewrite <- CR_of_Q_one. apply CR_of_Q_lt; reflexivity.
      apply CRlt_asym.
      apply CRmult_lt_0_compat. apply c0.
      apply CR_of_Q_pos; reflexivity.
      rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      reflexivity.
    + specialize (c1 (f x) (x + (cont_mod (f x) abs) * CR_of_Q R (1#2)) x abs).
      apply (CRle_abs (f x)).
      apply (CRle_lt_trans
               _ (CRabs _ (f (x + cont_mod (f x) abs * CR_of_Q R (1 # 2)) - f x))).
      rewrite (c (x + cont_mod (f x) abs * CR_of_Q R (1#2))).
      unfold CRminus. rewrite CRplus_0_l, CRabs_opp.
      apply CRle_refl. right. apply (CRle_lt_trans _ (x + 0)).
      rewrite CRplus_0_r. exact c2. apply CRplus_lt_compat_l.
      apply CRmult_lt_0_compat. apply c0.
      apply CR_of_Q_pos; reflexivity.
      apply c1.
      setoid_replace (x + (cont_mod (f x) abs * CR_of_Q R (1#2)) + - x)
        with (cont_mod (f x) abs * CR_of_Q R (1#2)).
      rewrite CRabs_right. rewrite <- (CRmult_1_r (cont_mod (f x) abs)).
      rewrite CRmult_assoc. apply CRmult_lt_compat_l. apply c0.
      rewrite CRmult_1_l. rewrite <- CR_of_Q_one. apply CR_of_Q_lt; reflexivity.
      apply CRlt_asym.
      apply CRmult_lt_0_compat. apply c0.
      apply CR_of_Q_pos; reflexivity.
      rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      reflexivity.
Qed.

Lemma UC_constant : forall {R : ConstructiveReals} (c : CRcarrier R),
    UniformCont (fun _:CRcarrier R => c) (fun _ _ => 1).
Proof.
  split. intros. apply CRzero_lt_one.
  intros. unfold CRminus.
  rewrite CRplus_opp_r, CRabs_right.
  exact epsPos. apply CRle_refl.
Qed.

Lemma eps2_Rgt_R0 : forall {R : ConstructiveReals} (eps : CRcarrier R),
    0 < eps -> 0 < eps * CR_of_Q R (1#2).
Proof.
  intros.
  apply CRmult_lt_0_compat. apply H.
  apply CR_of_Q_pos; reflexivity.
Qed.

Lemma UC_plus : forall {R : ConstructiveReals} (f g : CRcarrier R -> CRcarrier R)
                  (modF modG : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    UniformCont f modF
    -> UniformCont g modG
    -> UniformCont (fun x:CRcarrier R => f x + g x)
                  (fun eps epsPos => CRmin (modF (eps * CR_of_Q R (1#2)) (eps2_Rgt_R0 eps epsPos))
                                       (modG (eps * CR_of_Q R (1#2)) (eps2_Rgt_R0 eps epsPos))).
Proof.
  split.
  - intros. apply CRmin_lt. destruct H. apply c.
    destruct H0. apply c.
  - intros.
    setoid_replace (f x + g x - (f y + g y))
      with (f x - f y + (g x - g y)).
    apply (CRle_lt_trans _ _ _ (CRabs_triang _ _)).
    setoid_replace eps with (eps* CR_of_Q R (1#2) + eps* CR_of_Q R (1#2)).
    apply CRplus_le_lt_compat. apply CRlt_asym.
    destruct H.
    apply (c0 _ _ _ (eps2_Rgt_R0 eps epsPos)).
    apply (CRlt_le_trans
             _ (CRmin (modF (eps * CR_of_Q R (1#2)) (eps2_Rgt_R0 eps epsPos))
                      (modG (eps * CR_of_Q R (1#2)) (eps2_Rgt_R0 eps epsPos)))).
    apply H1. apply CRmin_l.
    destruct H0. apply (c0 _ _ _ (eps2_Rgt_R0 eps epsPos)).
    apply (CRlt_le_trans
             _ (CRmin (modF (eps * CR_of_Q R (1#2)) (eps2_Rgt_R0 eps epsPos))
                      (modG (eps * CR_of_Q R (1#2)) (eps2_Rgt_R0 eps epsPos)))).
    apply H1. apply CRmin_r.
    rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus.
    setoid_replace ((1 # 2) + (1#2))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_r.
    reflexivity. reflexivity.
    unfold CRminus. do 2 rewrite CRplus_assoc. apply CRplus_morph.
    reflexivity. rewrite CRplus_comm, CRopp_plus_distr.
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    rewrite CRplus_comm. reflexivity.
Qed.

Fixpoint UC_sum {R : ConstructiveReals} (fn : nat -> CRcarrier R -> CRcarrier R)
         (fnMod : nat -> forall x:CRcarrier R, 0 < x -> CRcarrier R)
         (fnCont : forall n:nat, UniformCont (fn n) (fnMod n))
         (n : nat)
  : { sMod : forall x:CRcarrier R, 0 < x -> CRcarrier R
    & UniformCont (fun x:CRcarrier R => CRsum (fun i => fn i x) n) sMod }.
Proof.
  destruct n.
  - exists (fnMod O). apply fnCont.
  - destruct (UC_sum R fn fnMod fnCont n) as [sMod sCont].
    exists (fun eps epsPos => CRmin (sMod (eps* CR_of_Q R (1#2)) (eps2_Rgt_R0 eps epsPos))
                            (fnMod (S n) (eps* CR_of_Q R (1#2)) (eps2_Rgt_R0 eps epsPos))).
    simpl. apply UC_plus. apply sCont. apply fnCont.
Qed.

Lemma UC_translate : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
                       (a : CRcarrier R)
                       (modF : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    UniformCont f modF
    -> UniformCont (fun x:CRcarrier R => f x + a) modF.
Proof.
  split. apply H. intros.
  setoid_replace (f x + a - (f y + a)) with (f x - f y).
  destruct H. apply (c0 _ _ _ epsPos). apply H0.
  unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
  reflexivity.
  rewrite CRplus_comm, CRopp_plus_distr.
  rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
Qed.

Lemma UC_translate_horizontal
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (a : CRcarrier R)
      (modF : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    UniformCont f modF
    -> UniformCont (fun x:CRcarrier R => f (x + a)) modF.
Proof.
  split. apply H. intros.
  destruct H. apply (c0 _ _ _ epsPos).
  setoid_replace (x + a - (y + a)) with (x-y).
  apply H0.
  unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
  reflexivity.
  rewrite CRplus_comm, CRopp_plus_distr.
  rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
Qed.

Lemma UC_modExt : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
                    (modF modG : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    UniformCont f modF
    -> (forall x xPos, modF x xPos == modG x xPos)
    -> UniformCont f modG.
Proof.
  split.
  - intros. rewrite <- H0. destruct H. apply c.
  - intros. rewrite <- H0 in H1. destruct H.
    apply (c0 _ _ _ epsPos). apply H1.
Qed.

Lemma UC_ext : forall {R : ConstructiveReals} (f g : CRcarrier R -> CRcarrier R)
                 (modF : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    UniformCont f modF
    -> (forall x:CRcarrier R, f x == g x)
    -> UniformCont g modF.
Proof.
  intros. destruct H. split.
  - apply c.
  - intros. do 2 rewrite <- H0. exact (c0 eps x y epsPos H).
Qed.

Lemma posScale : forall {R : ConstructiveReals} (a : CRcarrier R),
    0 < CRmax 1 (CRabs _ a).
Proof.
  intros. apply (CRlt_le_trans 0 1).
  apply CRzero_lt_one. apply CRmax_l.
Qed.

Lemma UC_scale : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
                   (modF : forall x:CRcarrier R, 0 < x -> CRcarrier R)
                   (a : CRcarrier R),
    UniformCont f modF
    -> UniformCont
        (fun x:CRcarrier R => a * f x)
        (fun (eps:CRcarrier R) epsPos => modF (eps * (CRinv R (CRmax 1 (CRabs _ a)) (inr (posScale a))))
                                     (CRmult_lt_0_compat _
                                        eps _ epsPos (CRinv_0_lt_compat _
                                                        _ (inr (posScale a)) (posScale a)))).
Proof.
  split.
  - intros x xPos. destruct H. apply c.
  - intros. unfold CRminus.
    rewrite CRopp_mult_distr_r, <- CRmult_plus_distr_l.
    rewrite CRabs_mult.
    apply (CRle_lt_trans
             _ (CRmax 1 (CRabs _ a) * CRabs _ (f x - f y))).
    apply CRmult_le_compat_r. apply CRabs_pos. apply CRmax_r.
    destruct H. specialize (c0 _ _ _ _ H0).
    apply (CRmult_lt_compat_r (CRmax 1 (CRabs _ a))) in c0.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_r in c0.
    rewrite CRmult_comm. exact c0. apply posScale.
Qed.

Lemma TelescopicSum : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (n : nat),
    CRsum (fun k => un (S k) - un k) n == un (S n) - (un O).
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite CRplus_comm.
    unfold CRminus. rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity.
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.

Lemma Rsum_minus : forall {R : ConstructiveReals} (un vn : nat -> CRcarrier R) (n : nat),
    CRsum (fun k => un k - vn k) n
    == CRsum un n - CRsum vn n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn.
    unfold CRminus. do 2 rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity. rewrite CRplus_comm.
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    rewrite CRplus_comm, CRopp_plus_distr. reflexivity.
Qed.

Lemma Rsmaller_interval : forall {R : ConstructiveReals} (a b c d : CRcarrier R),
    a <= c -> c <= b
    -> a <= d -> d <= b
    -> CRabs _ (d - c) <= b-a.
Proof.
  intros. apply CRabs_le. split.
  - apply (CRplus_le_reg_l (c+b)).
    unfold CRminus. rewrite CRopp_plus_distr.
    rewrite CRplus_assoc, <- (CRplus_assoc b).
    rewrite CRplus_opp_r, (CRplus_comm c b), CRplus_assoc.
    apply CRplus_le_compat. exact H0.
    rewrite CRopp_involutive, CRplus_0_l, CRplus_comm.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. exact H1.
  - apply (CRplus_le_reg_r (a+c)).
    unfold CRminus. rewrite (CRplus_assoc b), <- (CRplus_assoc (-a)).
    rewrite CRplus_opp_l, CRplus_0_l, CRplus_assoc.
    apply CRplus_le_compat. exact H2. rewrite CRplus_comm.
    rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r. exact H.
Qed.

Lemma sum_by_packets
  : forall {R : ConstructiveReals} (xn : nat -> CRcarrier R) (Pn : nat -> nat) (n : nat),
    (forall k, le k n -> lt (Pn k) (Pn (S k)))
    -> Pn O = O
    -> CRsum (fun i => CRsum (fun k => xn (k + Pn i))%nat
                               (pred (Pn (S i) - Pn i))) n
      == CRsum xn (pred (Pn (S n))).
Proof.
  induction n.
  - intros. simpl. rewrite H0.
    replace (pred (Pn 1 - 0))%nat with (pred (Pn 1%nat)).
    apply CRsum_eq. intros. rewrite Nat.add_comm. reflexivity.
    rewrite Nat.sub_0_r. reflexivity.
  - intros.
    assert (forall k : nat, k <= n -> Pn k < Pn (S k))%nat.
    { intros. apply H. apply (le_trans _ n _ H1). apply le_S, le_refl. }
    specialize (IHn H1 H0). clear H1. simpl.
    rewrite IHn.
    destruct (Pn (S (S n)) - Pn (S n))%nat eqn:des.
    exfalso. apply Nat.sub_0_le in des.
    apply (le_not_lt _ _ des). apply H, le_refl. simpl.
    pose proof (H n). destruct (Pn (S n)).
    exfalso. apply (le_not_lt 0 (Pn n) (le_0_n _)). apply H1, le_S, le_refl.
    clear H1. simpl.
    rewrite (CRsum_eq (fun k : nat => xn (k + S n1)%nat)
                      (fun k : nat => xn (S n1 + k)%nat)).
    2: intros; rewrite Nat.add_comm; reflexivity.
    rewrite <- (sum_assoc xn n1).
    replace (S n1 + n0)%nat with (Init.Nat.pred (Pn (S (S n)))).
    reflexivity.
    pose proof (H (S n) (le_refl _)). destruct (Pn (S (S n))). exfalso.
    inversion H1.
    simpl. simpl in des.
    replace (S (n1 + n0)) with (n1 + S n0)%nat.
    2: apply Nat.add_succ_r.
    rewrite <- des. rewrite Nat.add_comm. rewrite Nat.sub_add.
    reflexivity. destruct (le_lt_dec n2 n1).
    apply Nat.sub_0_le in l. rewrite l in des. discriminate.
    apply (le_trans _ (S n1)). apply le_S, le_refl. exact l.
Qed.


(* TODO replace SubSeqCv *)
Lemma ShouldReplaceSubSeq : forall (sub : SubSeq) (n : nat),
    le n (proj1_sig sub n).
Proof.
  induction n.
  - apply le_0_n.
  - destruct sub; simpl. simpl in IHn. specialize (l n (S n) (le_refl _)).
    apply (le_trans _ (S (x n))). apply le_n_S, IHn. exact l.
Qed.

Lemma SubSeqCvMerge : forall {R : ConstructiveReals} (un : nat -> CRcarrier R)
                        (sub : nat -> nat) (l : CRcarrier R),
    (forall n:nat, le n (sub n))
    -> CR_cv R un l -> CR_cv R (fun n => un (sub n)) l.
Proof.
  intros. intros n. specialize (H0 n) as [p pmaj].
  exists p. intros. apply pmaj.
  apply (le_trans _ i _ H0), H.
Qed.

Lemma Qpower_positive : forall (q : Q) (n : nat),
    Qlt 0 q -> Qlt 0 (q^Z.of_nat n).
Proof.
  induction n.
  - intros. reflexivity.
  - intros. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite Qpower_plus.
    rewrite <- (Qmult_0_l q). apply Qmult_lt_r. exact H. exact (IHn H).
    intro abs. rewrite abs in H. inversion H.
Qed.

Lemma pow_inject_Q : forall {R : ConstructiveReals} (q : Q) (n : nat),
    ~(q == 0)%Q
     -> (CR_of_Q R (q ^ Z.of_nat n) == CRpow (CR_of_Q R q) n).
Proof.
  induction n.
  - intros. simpl. apply CR_of_Q_one.
  - intros. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite Qpower_plus.
    rewrite CR_of_Q_mult, IHn. simpl. apply CRmult_comm. exact H. exact H.
Qed.

Definition UCUnitHeaviside {R : ConstructiveReals}
           (a b : CRcarrier R) (ltab : a < b)
  : CRcarrier R -> CRcarrier R
  := fun x => (CRmax 0 (CRmin 1 ((x - a) * (CRinv R (b-a) (inr (CRlt_minus _ _ ltab)))))).

Lemma LipschitzMin
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
      (k m : CRcarrier R),
    Lipschitz f k
    -> Lipschitz (fun x => CRmin m (f x)) k.
Proof.
  intros R f k m fl x y.
  rewrite CRmin_sym, (CRmin_sym m).
  apply (CRle_trans _ _ _ (CRmin_contract _ _ _)).
  apply fl.
Qed.

Lemma UCmin : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
                (m : CRcarrier R)
                (fMod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R),
    0 <= m
    -> UniformCont f fMod -> UniformCont (fun x => CRmin m (f x)) fMod.
Proof.
  intros R f m fMod mPos H. destruct H. split. exact c.
  intros. apply (CRle_lt_trans _ (CRabs _ (f x - f y))).
  2: apply (c0 eps _ _ epsPos H).
  rewrite CRmin_sym, (CRmin_sym m). apply CRmin_contract.
Qed.

Lemma UCmax : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
                (m : CRcarrier R)
                (fMod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R),
    0 <= m
    -> UniformCont f fMod -> UniformCont (fun x => CRmax m (f x)) fMod.
Proof.
  intros R f m fMod mPos H. destruct H. split. exact c.
  intros. apply (CRle_lt_trans _ (CRabs _ (f x - f y))).
  2: apply (c0 eps _ _ epsPos H).
  rewrite CRmax_sym, (CRmax_sym m). apply CRmax_contract.
Qed.

Lemma UCHeaviside_cont
  : forall {R : ConstructiveReals} (a b : CRcarrier R) (ltab : a < b),
    UniformCont (UCUnitHeaviside a b ltab)
                (fun eps epsPos => eps * (b-a)).
Proof.
  intros.
  apply UCmax. apply CRle_refl. apply UCmin. apply CRlt_asym, CRzero_lt_one.
  assert (0 < (b - a)). apply CRlt_minus. apply ltab.
  split.
  - intros. apply CRmult_lt_0_compat; assumption.
  - intros.
    rewrite (CRabs_morph
               _ ((x - y) * (CRinv R (b - a) (inr (CRlt_minus a b ltab))))).
    rewrite CRabs_mult.
    rewrite (CRabs_right (CRinv R (b - a) (inr (CRlt_minus a b ltab)))).
    apply (CRlt_le_trans
             _ (eps * (b-a) * (CRinv R (b - a) (inr (CRlt_minus a b ltab))))).
    apply CRmult_lt_compat_r. 2: exact H0.
    apply CRinv_0_lt_compat, H.
    rewrite CRmult_assoc, CRinv_r, CRmult_1_r. apply CRle_refl.
    apply CRlt_asym, CRinv_0_lt_compat, H.
    unfold CRminus. rewrite CRopp_mult_distr_l.
    rewrite <- CRmult_plus_distr_r.
    setoid_replace (x + - a + - (y + - a)) with (x+-y). reflexivity.
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    rewrite CRplus_comm, CRopp_plus_distr.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
Qed.

Lemma UCHeavisideBounded : forall {R : ConstructiveReals} (a b x : CRcarrier R)
                             (ltab : a < b),
    (0 <= UCUnitHeaviside a b ltab x <= 1).
Proof.
  intros. unfold UCUnitHeaviside. split.
  - apply CRmax_l.
  - apply CRmax_lub. apply CRlt_asym, CRzero_lt_one. apply CRmin_l.
Qed.

Lemma Rplus_pos_higher : forall {R : ConstructiveReals} (a eps:CRcarrier R),
    0 < eps -> a < (a+eps).
Proof.
  intros.
  rewrite <- (CRplus_0_r a). rewrite CRplus_assoc.
  apply CRplus_lt_compat_l. rewrite CRplus_0_l.
  exact H.
Qed.

Lemma Rminus_pos_lower : forall {R : ConstructiveReals} (a eps:CRcarrier R),
    0 < eps -> (a-eps) < a.
Proof.
  intros. apply (CRplus_lt_reg_r eps).
  unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
  apply Rplus_pos_higher. apply H.
Qed.

Definition CSUCUnitTrapeze {R : ConstructiveReals}
           (a b eta : CRcarrier R) (etaPos : 0 < eta)
           (x : CRcarrier R) : CRcarrier R
  := UCUnitHeaviside (a-eta) a (Rminus_pos_lower a eta etaPos) x
     - UCUnitHeaviside b (b+eta) (Rplus_pos_higher b eta etaPos) x.

Lemma CSUCUnitTrapeze_cont
  : forall {R : ConstructiveReals} (a b eta : CRcarrier R) (etaPos : 0 < eta),
    a <= b -> UniformCont (CSUCUnitTrapeze a b eta etaPos)
                        (* The modulus could be improved to eps*eta *)
                        (fun eps epsPos => eps * CR_of_Q R (1#2) * eta).
Proof.
  intros.
  apply (UC_modExt _ (fun eps epsPos =>
                        CRmin (eps * CR_of_Q R (1#2) * (a - (a - eta)))
                              (eps * CR_of_Q R (1#2) * (b + eta - b)))).
  - apply (UC_plus _ _
                   (fun eps epsPos => eps * (a-(a-eta)))
                   (fun eps epsPos => eps * (b+eta-b))).
    apply UCHeaviside_cont. split.
    intros. rewrite CRplus_comm. unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    rewrite <- (CRmult_0_r x). apply CRmult_lt_compat_l.
    exact xPos. exact etaPos.
    intros. unfold CRminus.
    rewrite <- CRopp_plus_distr. rewrite CRabs_opp.
    apply UCHeaviside_cont. apply epsPos. apply H0.
  - intros. rewrite CRmin_left.
    unfold CRminus.
    rewrite CRopp_plus_distr, <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite CRopp_involutive. reflexivity.
    setoid_replace (a - (a - eta)) with eta.
    setoid_replace (b + eta - b) with eta. apply CRle_refl.
    unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
    rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
    unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
    rewrite CRplus_opp_r, CRplus_0_l, CRopp_involutive. reflexivity.
Qed.

Lemma UCHeavisideIn : forall {R : ConstructiveReals} (a b x : CRcarrier R) (altb : a < b),
    b <= x -> UCUnitHeaviside a b altb x == 1.
Proof.
  intros. unfold UCUnitHeaviside.
  rewrite CRmin_left, CRmax_right. reflexivity.
  apply CRlt_asym, CRzero_lt_one.
  apply (CRmult_le_reg_r (b-a)).
  unfold CRminus. rewrite <- (CRplus_opp_r a).
  apply CRplus_lt_compat_r. exact altb.
  rewrite CRmult_assoc, CRinv_l, CRmult_1_l, CRmult_1_r.
  unfold CRminus. rewrite CRplus_comm, (CRplus_comm x).
  apply CRplus_le_compat_l. apply H.
Qed.

Lemma CSUCTrapezePlateau
  : forall {R : ConstructiveReals} (a b eta x : CRcarrier R) (etaPos : 0 < eta),
    (a <= x <= b) -> CSUCUnitTrapeze a b eta etaPos x == 1.
Proof.
  intros. unfold CSUCUnitTrapeze. rewrite UCHeavisideIn. 2: apply H.
  unfold UCUnitHeaviside. rewrite CRmax_left.
  unfold CRminus. rewrite CRopp_0, CRplus_0_r. reflexivity.
  apply (CRle_trans _ _ _ (CRmin_r _ _)).
  apply (CRmult_le_reg_r (b+eta-b)).
  unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
  rewrite CRplus_opp_l, CRplus_0_l. apply etaPos.
  rewrite CRmult_assoc, CRinv_l, CRmult_0_l, CRmult_1_r.
  unfold CRminus. rewrite CRplus_comm.
  rewrite <- (CRplus_opp_l b). apply CRplus_le_compat_l. apply H.
Qed.

Lemma CSUCTrapezeInPlateau
  : forall {R : ConstructiveReals} (a b eta x : CRcarrier R) (etaPos : 0 < eta),
    0 < CSUCUnitTrapeze a b eta etaPos x
    -> (a-eta < x < b+eta).
Proof.
  intros. unfold CSUCUnitTrapeze in H.
  apply (CRplus_lt_compat_r
           (UCUnitHeaviside b (b + eta) (Rplus_pos_higher b eta etaPos) x)) in H.
  unfold CRminus in H.
  rewrite CRplus_0_l, CRplus_assoc, CRplus_opp_l, CRplus_0_r in H.
  split.
  - assert (0 < UCUnitHeaviside (a - eta) a (Rminus_pos_lower a eta etaPos) x).
    { apply (CRle_lt_trans
               _ (UCUnitHeaviside b (b + eta) (Rplus_pos_higher b eta etaPos) x)).
      2: exact H. apply UCHeavisideBounded. }
    unfold UCUnitHeaviside in H0.
    rewrite CRmax_right in H0. apply CRlt_min in H0. destruct H0.
    apply (CRmult_lt_compat_r (a-(a-eta))) in c0.
    rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r in c0.
    rewrite <- (CRplus_opp_r (a-eta)) in c0. apply CRplus_lt_reg_r in c0.
    exact c0. unfold CRminus.
    rewrite CRopp_plus_distr, <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite CRopp_involutive. exact etaPos.
    intro abs. rewrite CRmax_left in H0. exact (CRlt_asym 0 0 H0 H0).
    apply CRlt_asym, abs.
  - assert (UCUnitHeaviside b (b+eta) (Rplus_pos_higher b eta etaPos) x < 1).
    { apply (CRlt_le_trans _ _ _ H). apply UCHeavisideBounded. }
    unfold UCUnitHeaviside in H0. apply CRlt_max in H0. destruct H0 as [_ H0].
    rewrite CRmin_right in H0.
    apply (CRmult_lt_compat_r (b+eta-b)) in H0.
    rewrite CRmult_1_l, CRmult_assoc, CRinv_l, CRmult_1_r in H0.
    apply CRplus_lt_reg_r in H0. exact H0. unfold CRminus.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
    exact etaPos.
    intro abs. rewrite CRmin_left in H0. exact (CRlt_asym 1 1 H0 H0).
    apply CRlt_asym, abs.
Qed.

Lemma CSUCTrapezePositive
  : forall {R : ConstructiveReals} (a b eta x : CRcarrier R)
      (etaPos : 0 < eta) (leab : a <= b),
    prod (a-eta < x) (x < b+eta)
    -> 0 < (CSUCUnitTrapeze a b eta etaPos x).
Proof.
  intros. unfold CSUCUnitTrapeze, UCUnitHeaviside.
  rewrite CRmax_right.
  rewrite (CRmin_right
             1 ((x - b) *
        CRinv R (b + eta - b) (inr (CRlt_minus b (b + eta) (Rplus_pos_higher b eta etaPos))))).
  - apply (CRle_lt_trans
             _ (CRmax 0
    ((x - b) *
     CRinv R (b + eta - b) (inr (CRlt_minus b (b + eta) (Rplus_pos_higher b eta etaPos))))
                            - CRmax 0
    ((x - b) *
     CRinv R (b + eta - b) (inr (CRlt_minus b (b + eta) (Rplus_pos_higher b eta etaPos)))))).
    unfold CRminus. rewrite CRplus_opp_r. apply CRle_refl.
    apply CRplus_lt_compat_r.
    apply CRmin_lt. apply CRmax_lub_lt. apply CRzero_lt_one.
    2: apply CRmax_lub_lt.
    + apply (CRmult_lt_reg_r (b+eta-b)).
      unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l. exact etaPos.
      rewrite CRmult_assoc, CRinv_l, CRmult_1_l, CRmult_1_r.
      unfold CRminus. apply CRplus_lt_compat_r. apply H.
    + apply (CRmult_lt_reg_r (a-(a-eta))).
      unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
      rewrite CRplus_opp_r, CRplus_0_l, CRopp_involutive. exact etaPos.
      rewrite CRmult_assoc, CRinv_l, CRmult_0_l, CRmult_1_r.
      rewrite <- (CRplus_opp_r (a-eta)).
      apply CRplus_lt_compat_r. apply H.
    + apply (CRmult_lt_reg_r (b+eta-b)).
      unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l. exact etaPos.
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r.
      setoid_replace (b + eta - b) with eta.
      rewrite <- (CRmult_comm eta).
      apply (CRmult_lt_reg_r (a-(a-eta))).
      unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
      rewrite CRplus_opp_r, CRplus_0_l, CRopp_involutive. exact etaPos.
      rewrite CRmult_assoc, CRmult_assoc, CRinv_l, CRmult_1_r.
      setoid_replace (a - (a - eta)) with eta.
      rewrite CRmult_comm. apply CRmult_lt_compat_l. exact etaPos.
      apply CRplus_lt_compat_l. apply CRopp_gt_lt_contravar.
      apply (CRlt_le_trans _ a). apply (CRplus_lt_reg_r eta).
      unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l.
      apply CRplus_lt_compat_l, etaPos. exact leab.
      unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
      rewrite CRplus_opp_r, CRplus_0_l, CRopp_involutive. reflexivity.
      unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
  - apply (CRmult_le_reg_r (b+eta-b)).
    unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
    rewrite CRplus_opp_l, CRplus_0_l. exact etaPos.
    rewrite CRmult_assoc, CRinv_l, CRmult_1_l, CRmult_1_r.
    unfold CRminus. rewrite CRplus_comm.
    rewrite <- (CRplus_comm (-b)). apply CRplus_le_compat_l.
    apply CRlt_asym, H.
  - apply CRmin_glb. apply CRlt_asym, CRzero_lt_one.
    apply (CRmult_le_reg_r (a-(a-eta))).
    unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
    rewrite CRplus_opp_r, CRplus_0_l, CRopp_involutive. exact etaPos.
    rewrite CRmult_assoc, CRinv_l, CRmult_0_l, CRmult_1_r.
    unfold CRminus.
    rewrite <- (CRplus_opp_l (a-eta)), (CRplus_comm x).
    apply CRplus_le_compat_l. apply CRlt_asym, H.
Qed.

Lemma CSUCTrapezeBounded
  : forall {R : ConstructiveReals} (a b eta x : CRcarrier R) (etaPos : 0 < eta),
    a <= b
    -> (0 <= CSUCUnitTrapeze a b eta etaPos x <= 1).
Proof.
  intros. unfold CSUCUnitTrapeze, UCUnitHeaviside.
  rewrite (CRinv_morph (a - (a-eta)) eta _ (inr etaPos)).
  rewrite (CRinv_morph (b + eta - b) eta _ (inr etaPos)).
  destruct (CRltLinear R). destruct (s a x (b+eta)).
  - apply (CRle_lt_trans _ (b+0)). rewrite CRplus_0_r. exact H.
    apply CRplus_lt_compat_l. exact etaPos.
  - (* a < x *)
    rewrite CRmax_right, CRmin_left.
    split.
    + apply (CRle_trans _ (1-1)).
      unfold CRminus. rewrite CRplus_opp_r. apply CRle_refl.
      apply CRplus_le_compat_l. apply CRopp_ge_le_contravar.
      apply CRmax_lub. apply CRlt_asym, CRzero_lt_one. apply CRmin_l.
    + apply (CRle_trans _ (1-0)). apply CRplus_le_compat_l.
      apply CRopp_ge_le_contravar. apply CRmax_l.
      unfold CRminus. rewrite CRopp_0, CRplus_0_r. apply CRle_refl.
    + unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive.
      rewrite <- CRplus_assoc, CRmult_plus_distr_r, CRinv_r.
      apply (CRle_trans _ (0+1)). rewrite CRplus_0_l. apply CRle_refl.
      apply CRplus_le_compat_r. apply (CRle_trans _ ((x-a)*0)).
      rewrite CRmult_0_r. apply CRle_refl. apply CRlt_asym.
      apply CRmult_lt_compat_l.
      rewrite <- (CRplus_opp_r a). apply CRplus_lt_compat_r, c.
      apply CRinv_0_lt_compat. exact etaPos.
    + apply CRmin_glb.
      apply CRlt_asym, CRzero_lt_one.
      apply (CRle_trans _ ((x-(a-eta))*0)).
      rewrite CRmult_0_r. apply CRle_refl. apply CRlt_asym.
      apply CRmult_lt_compat_l.
      apply (CRplus_lt_reg_r (a-eta)). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_0_l.
      apply (CRlt_trans _ a). 2: apply c.
      apply (CRplus_lt_reg_r eta). rewrite CRplus_assoc, CRplus_opp_l.
      apply CRplus_lt_compat_l. exact etaPos.
      apply CRinv_0_lt_compat. exact etaPos.
  - rewrite (CRmin_right 1 ((x - b) * CRinv R eta (inr etaPos))). split.
    + unfold CRminus. rewrite CRplus_comm.
      apply (CRle_trans _ (-(CRmax 0 ((x - b) * CRinv R eta (inr etaPos)))
                           + CRmax 0 ((x - b)* CRinv R eta (inr etaPos)))).
      rewrite CRplus_opp_l. apply CRle_refl.
      apply CRplus_le_compat_l.
      apply CRmax_lub. apply CRmax_l.
      apply (CRle_trans
               _ (CRmin 1 ((x + - (a + - eta)) * CRinv R eta (inr etaPos)))).
      2: apply CRmax_r. apply CRmin_glb.
      apply (CRmult_le_reg_r eta _ 1). exact etaPos.
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_1_l.
      apply (CRplus_le_reg_r b). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      rewrite CRplus_comm. apply CRlt_asym, c.
      apply CRmult_le_compat_r.
      apply CRlt_asym, CRinv_0_lt_compat. exact etaPos.
      apply CRplus_le_compat_l. apply CRopp_ge_le_contravar.
      apply (CRplus_le_reg_r eta).
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply (CRle_trans _ (b+0)). rewrite CRplus_0_r. exact H.
      apply CRplus_le_compat_l. apply CRlt_asym, etaPos.
    + apply (CRplus_le_reg_r (CRmax 0 ((x - b) * CRinv R eta (inr etaPos)))).
      unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply CRmax_lub. apply (CRle_trans _ (1+0)).
      rewrite CRplus_0_r. apply CRlt_asym, CRzero_lt_one.
      apply CRplus_le_compat_l. apply CRmax_l.
      apply (CRle_trans _ (1+0)).
      rewrite CRplus_0_r. apply CRmin_l.
      apply CRplus_le_compat_l. apply CRmax_l.
    + apply (CRmult_le_reg_r eta _ 1). exact etaPos.
      rewrite CRmult_assoc, CRinv_l, CRmult_1_l, CRmult_1_r.
      apply (CRplus_le_reg_r b).
      unfold CRminus. rewrite CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_r.
      rewrite CRplus_comm. apply CRlt_asym, c.
  - unfold CRminus. rewrite CRplus_comm.
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
  - unfold CRminus. rewrite CRopp_plus_distr.
    rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l.
    rewrite CRopp_involutive. reflexivity.
Qed.

Lemma TrapezeIncluded
  : forall {R : ConstructiveReals} (a b c d eta mu x : CRcarrier R)
           (etaPos : 0 < eta) (muPos : 0 < mu),
    a - eta == c - mu
    -> b + eta == d + mu
    -> eta <= mu
    -> CSUCUnitTrapeze c d mu muPos x
       <= CSUCUnitTrapeze a b eta etaPos x.
Proof.
  intros.
  assert (CRinv R mu (inr muPos) <= CRinv R eta (inr etaPos)) as invLe.
  { apply (CRmult_le_reg_l mu _ _ muPos). rewrite CRinv_r.
    apply (CRmult_le_reg_r eta _ _ etaPos).
    rewrite CRmult_1_l, CRmult_assoc, CRinv_l, CRmult_1_r. exact H1. }
  apply CRplus_le_compat.
  - unfold UCUnitHeaviside.
    rewrite (CRinv_morph (a - (a-eta)) eta _ (inr etaPos)).
    rewrite (CRinv_morph (c - (c-mu)) mu _ (inr muPos)).
    apply CRmax_lub. apply CRmax_l. rewrite <- H.
    destruct (CRltLinear R). destruct (s (a-eta) x a).
    + apply (CRplus_lt_reg_r eta). unfold CRminus.
      rewrite CRplus_assoc. apply CRplus_lt_compat_l.
      rewrite CRplus_opp_l. exact etaPos.
    + apply (CRle_trans _ (CRmin 1 ((x - (a - eta)) * CRinv R eta (inr etaPos)))).
      2: apply CRmax_r. apply CRmin_glb. apply CRmin_l.
      apply (CRle_trans _ ((x - (a - eta)) * CRinv R mu (inr muPos))).
      apply CRmin_r. apply CRmult_le_compat_l.
      rewrite <- (CRplus_opp_r (a-eta)). apply CRplus_le_compat_r, CRlt_asym, c0.
      exact invLe.
    + rewrite CRmin_right. rewrite CRmin_right.
      apply (CRmult_le_reg_r mu _ _ muPos).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRle_trans
               _ (eta * CRmax 0 ((x - (a - eta)) * CRinv R eta (inr etaPos)))).
      rewrite <- CRmax_mult. rewrite CRmult_0_r, CRmult_comm.
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r. apply CRmax_r.
      apply CRlt_asym, etaPos. rewrite CRmult_comm.
      apply CRmult_le_compat_l. apply CRmax_l. exact H1.
      apply (CRmult_le_reg_r eta _ _ etaPos).
      rewrite CRmult_1_l, CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRplus_le_reg_l a). unfold CRminus.
      rewrite CRopp_plus_distr, CRopp_involutive, <- CRplus_assoc, <- CRplus_assoc.
      apply CRplus_le_compat_r.
      rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      apply CRlt_asym, c0.
      apply (CRmult_le_reg_r mu _ _ muPos).
      rewrite CRmult_1_l, CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRle_trans _ eta).
      apply (CRplus_le_reg_l a). unfold CRminus.
      rewrite CRopp_plus_distr, CRopp_involutive, <- CRplus_assoc, <- CRplus_assoc.
      apply CRplus_le_compat_r.
      rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      apply CRlt_asym, c0. exact H1.
    + unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive, <- CRplus_assoc.
      rewrite CRplus_opp_r, CRplus_0_l. reflexivity.
    + unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive, <- CRplus_assoc.
      rewrite CRplus_opp_r, CRplus_0_l. reflexivity.
  - apply CRopp_ge_le_contravar. unfold UCUnitHeaviside.
    rewrite (CRinv_morph (b + eta - b) eta _ (inr etaPos)).
    rewrite (CRinv_morph (d + mu - d) mu _ (inr muPos)).
    apply CRmax_lub. apply CRmax_l.
    destruct (CRltLinear R). destruct (s b x (b+eta)).
    + apply (CRplus_lt_reg_r 0).
      rewrite CRplus_assoc. apply CRplus_lt_compat_l.
      rewrite CRplus_0_r. exact etaPos.
    + apply (CRle_trans _ (CRmin 1 ((x - d) * CRinv R mu (inr muPos)))).
      2: apply CRmax_r. apply CRmin_glb. apply CRmin_l.
      apply (CRmult_le_reg_r mu _ _ muPos).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_comm.
      rewrite <- (CRplus_0_r 1).
      setoid_replace ((x - b) * CRinv R eta (inr etaPos))
        with (1 + (x - (b+eta)) * CRinv R eta (inr etaPos)).
      rewrite <- CRmin_plus, CRmult_plus_distr_l, CRmult_1_r.
      apply (CRplus_le_reg_l (-mu)).
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l.
      apply (CRle_trans _ (x - (b + eta))).
      assert (0 == CRinv R eta (inr etaPos) * 0).
      symmetry. apply CRmult_0_r. rewrite (CRmult_comm (x - (b + eta))).
      rewrite (CRmin_morph R 0 (CRinv R eta (inr etaPos) * 0) H2 _ _ (CReq_refl _)).
      rewrite CRmin_mult. apply (CRle_trans _ (CRmin 0 (x - (b + eta)))).
      2: apply CRmin_r.
      rewrite <- CRopp_involutive, <- (CRopp_involutive (CRmin 0 (x - (b + eta)))).
      apply CRopp_ge_le_contravar.
      rewrite CRopp_involutive, CRopp_mult_distr_r, CRopp_mult_distr_r.
      rewrite <- (CRmult_1_l (- CRmin 0 (x - (b + eta)))), <- CRmult_assoc.
      rewrite <- CRmult_assoc. apply CRmult_le_compat_r.
      rewrite <- CRopp_0. apply CRopp_ge_le_contravar.
      apply (CRle_trans _ (-0)). apply CRmin_l. rewrite CRopp_0. apply CRle_refl.
      rewrite CRmult_1_r. apply (CRmult_le_reg_r eta _ _ etaPos).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_1_l. exact H1.
      apply CRlt_asym, CRinv_0_lt_compat, etaPos.
      unfold CRminus. rewrite H0, CRopp_plus_distr, (CRplus_comm (-mu)).
      rewrite CRplus_assoc. apply CRle_refl.
      unfold CRminus. rewrite (CRplus_comm 1), CRmult_plus_distr_r.
      rewrite CRmult_plus_distr_r, CRopp_plus_distr, CRmult_plus_distr_r.
      rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
      rewrite <- (CRopp_mult_distr_l eta), CRinv_r.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
    + rewrite CRmin_right. rewrite CRmin_right.
      apply (CRle_trans _ ((x - d) * CRinv R mu (inr muPos))). 2: apply CRmax_r.
      apply (CRplus_le_reg_r (-(1))).
      apply (CRle_trans _ ((x - (b+eta)) * CRinv R eta (inr etaPos))).
      unfold CRminus. do 2 rewrite CRmult_plus_distr_r.
      rewrite CRopp_plus_distr, CRmult_plus_distr_r, <- (CRopp_mult_distr_l eta).
      rewrite CRinv_r, <- CRplus_assoc. apply CRle_refl.
      apply (CRle_trans _ ((x - (d+mu)) * CRinv R mu (inr muPos))).
      rewrite <- H0. rewrite <- CRopp_involutive.
      rewrite <- (CRopp_involutive ((x - (b + eta)) * CRinv R mu (inr muPos))).
      apply CRopp_ge_le_contravar. do 2 rewrite CRopp_mult_distr_l.
      apply CRmult_le_compat_l. unfold CRminus.
      rewrite CRopp_plus_distr, CRopp_involutive, <- (CRplus_opp_l x).
      apply CRplus_le_compat_l. apply CRlt_asym, c0. exact invLe.
      unfold CRminus. do 2 rewrite CRmult_plus_distr_r.
      rewrite CRopp_plus_distr, CRmult_plus_distr_r, <- (CRopp_mult_distr_l mu).
      rewrite CRinv_r, <- CRplus_assoc. apply CRle_refl.
      apply (CRmult_le_reg_r mu _ _ muPos).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_1_l.
      apply (CRplus_le_reg_r d). unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l.
      rewrite CRplus_0_r, CRplus_comm, <- H0. apply CRlt_asym, c0.
      apply (CRmult_le_reg_r eta _ _ etaPos).
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r, CRmult_1_l.
      apply (CRplus_le_reg_r b). unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l.
      rewrite CRplus_0_r, CRplus_comm. apply CRlt_asym, c0.
    + unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
    + unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.

Lemma Rminus_plus_one_lower : forall {R : ConstructiveReals} (a b : CRcarrier R),
    a <= b -> (a-1) <= (b+1).
Proof.
  intros. apply (CRle_trans _ a).
  apply CRlt_asym, Rminus_pos_lower. apply CRzero_lt_one.
  apply (CRle_trans _ b _ H).
  apply CRlt_asym, Rplus_pos_higher. apply CRzero_lt_one.
Qed.

Lemma UC_x : forall {R : ConstructiveReals},
    UniformCont (fun x:CRcarrier R => x) (fun eps _ => eps).
Proof.
  split. intros. exact xPos. intros. exact H.
Qed.

Lemma S_INR : forall {R : ConstructiveReals} (n:nat),
    INR (S n) == @INR R n + 1.
Proof.
  intros R n. unfold INR. rewrite <- CR_of_Q_one, <- CR_of_Q_plus.
  apply CR_of_Q_morph. rewrite Qinv_plus_distr.
  unfold Qeq, Qnum, Qden. do 2 rewrite Z.mul_1_r.
  fold (1 + n)%nat.
  rewrite (Nat2Z.inj_add 1 n). rewrite Z.add_comm. reflexivity.
Qed.

Lemma sum_INR :
  forall {R : ConstructiveReals} (n:nat),
    CRsum INR n
    == INR n * (INR (S n)) * CR_of_Q R (1#2).
Proof.
  induction n.
  - unfold CRsum, INR, Z.of_nat. rewrite CR_of_Q_zero, CRmult_0_l, CRmult_0_l.
    reflexivity.
  - transitivity (CRsum INR n + @INR R (S n)).
    reflexivity. rewrite IHn. clear IHn.
    transitivity (INR (S n) * (INR n * CR_of_Q R (1#2) + 1)).
    rewrite CRmult_plus_distr_l. apply CRplus_morph.
    rewrite <- CRmult_assoc. apply CRmult_morph. 2: reflexivity.
    apply CRmult_comm. rewrite CRmult_1_r. reflexivity.
    rewrite CRmult_assoc. apply CRmult_morph.
    reflexivity.
    apply (CRmult_eq_reg_r (CR_of_Q R 2)).
    left. apply CR_of_Q_pos; reflexivity.
    rewrite CRmult_plus_distr_r, CRmult_1_l.
    rewrite CRmult_assoc, <- CR_of_Q_mult.
    rewrite CRmult_assoc, <- (CR_of_Q_mult _ (1#2)).
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CR_of_Q_one.
    do 2 rewrite CRmult_1_r. rewrite (CR_of_Q_plus R 1 1).
    do 2 rewrite S_INR. rewrite CRplus_assoc.
    rewrite CR_of_Q_one. reflexivity.
Qed.

Lemma CSUCTrapeze_CSUC
  : forall {R : ConstructiveReals} (a b eta : CRcarrier R) (etaPos : 0 < eta),
    a <= b -> CSUC (CSUCUnitTrapeze a b eta etaPos)
                 (a-eta) (b+eta) (fun eps epsPos => eps * CR_of_Q R (1#2) * eta).
Proof.
  intros. split.
  - apply CSUCUnitTrapeze_cont. apply H.
  - intros. unfold CSUCUnitTrapeze, UCUnitHeaviside.
    rewrite (CRinv_morph (a - (a-eta)) eta _ (inr etaPos)).
    rewrite (CRinv_morph (b + eta - b) eta _ (inr etaPos)).
    destruct H0 as [H0|H0].
    + assert (x < a).
      { apply (CRlt_trans x (a-eta)). apply H0.
        apply Rminus_pos_lower. exact etaPos. }
      assert (x < b).
      { exact (CRlt_le_trans x a _ H1 H). }
      rewrite CRmax_left, CRmax_left.
      unfold CRminus. rewrite CRplus_opp_r. reflexivity.
      apply (CRle_trans _ _ _ (CRmin_r _ _)).
      apply (CRmult_le_reg_r eta). exact etaPos.
      rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRplus_le_reg_r b). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_0_r.
      apply CRlt_asym, H2.
      apply (CRle_trans _ _ _ (CRmin_r _ _)).
      apply (CRmult_le_reg_r eta). exact etaPos.
      rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRplus_le_reg_r (a-eta)). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_0_r.
      apply CRlt_asym, H0.
    + assert (b < x).
      { apply (CRlt_trans b (b+eta)). apply Rplus_pos_higher.
        exact etaPos. apply H0. }
      assert (a < x).
      { exact (CRle_lt_trans a b _ H H1). }
      rewrite CRmax_right, CRmax_right.
      rewrite CRmin_left, CRmin_left.
      unfold CRminus. apply CRplus_opp_r.
      apply (CRmult_le_reg_r eta _ _ etaPos).
      rewrite CRmult_1_l, CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRplus_le_reg_r b). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_comm.
      apply CRlt_asym, H0.
      apply (CRmult_le_reg_r eta _ _ etaPos).
      rewrite CRmult_1_l, CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRplus_le_reg_r (a-eta)). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_comm.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      apply CRlt_asym, H2.
      apply CRmin_glb. apply CRlt_asym, CRzero_lt_one.
      apply (CRmult_le_reg_r eta _ _ etaPos).
      rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRplus_le_reg_r b). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_0_l.
      apply CRlt_asym, H1.
      apply CRmin_glb. apply CRlt_asym, CRzero_lt_one.
      apply (CRmult_le_reg_r eta _ _ etaPos).
      rewrite CRmult_0_l, CRmult_assoc, CRinv_l, CRmult_1_r.
      apply (CRplus_le_reg_r (a-eta)). unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r, CRplus_0_l.
      apply (CRle_trans _ a). 2: apply CRlt_asym, H2.
      apply (CRplus_le_reg_r eta).
      rewrite CRplus_assoc, CRplus_opp_l.
      apply CRplus_le_compat_l. apply CRlt_asym, etaPos.
    + unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
    + unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
      rewrite CRplus_opp_r, CRplus_0_l, CRopp_involutive. reflexivity.
Qed.

Definition UC_bounded {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
           (a b : CRcarrier R) (fMod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
           (fUC : UniformCont f fMod)
  : a <= b -> { B : CRcarrier R & forall x:CRcarrier R, a <= x -> x <= b -> CRabs _ (f x) < B }.
Proof.
  (* Evaluate the modulus of uniform continuity for 1,
     then divide the segment [a,b] by this length and
     take the highest value of f at those points, plus 1. *)
  pose proof ((snd fUC) 1). intros.
  (* Divide the modulus by 2, because constructively there is no exact
     comparison of real numbers. *)
  pose (nat_rec (fun n => CRcarrier R) (CRabs _ (f a))
                (fun n x => CRmax x (CRabs _ (f (a + INR (S n) * fMod 1 (CRzero_lt_one R) * CR_of_Q R (1#2))))))
    as maxou.
  assert (forall i k : nat, le i k
                     -> CRabs _ (f (a + INR i * fMod 1 (CRzero_lt_one R) * CR_of_Q R (1# 2)))
                       <= (maxou k))
    as maxouSpec.
  { induction k.
    - intros. inversion H1. unfold INR, Z.of_nat.
      rewrite (UniformContProper f fMod fUC _ a).
      apply CRle_refl. rewrite CR_of_Q_zero.
      rewrite CRmult_0_l. rewrite CRmult_0_l, CRplus_0_r. reflexivity.
    - intros. apply Nat.le_succ_r in H1. destruct H1.
      apply (CRle_trans _ (maxou k) _ (IHk H1)). apply CRmax_l.
      subst i. apply CRmax_r. }
  (* Get maximal index k of subdivision *)
  destruct (CRup_nat ((b - a) * CR_of_Q R 2
                     * (CRinv R (fMod 1 (CRzero_lt_one R)) (inr ((fst fUC) 1 (CRzero_lt_one R))))))
    as [k kmaj].
  exists (maxou k + 1). intros.
  assert (0 < fMod 1 (CRzero_lt_one R)) as stepPos.
  { apply (fst fUC). }
  (* Find 2 columns around x *)
  destruct (CRfloor ((x-a) * CR_of_Q R 2 * (CRinv R (fMod 1 (CRzero_lt_one R))
                                                  (inr ((fst fUC) 1 (CRzero_lt_one R))))))
    as [i [H4 H5]].
  apply (CRmult_lt_compat_r (fMod 1 (CRzero_lt_one R))) in H4.
  rewrite CRmult_assoc in H4. rewrite CRinv_l in H4.
  rewrite CRmult_1_r in H4.
  apply (CRmult_lt_compat_r (fMod 1 (CRzero_lt_one R))) in H5.
  rewrite CRmult_assoc in H5. rewrite CRinv_l in H5.
  rewrite CRmult_1_r in H5.
  2: apply (fst fUC).
  2: apply (fst fUC). apply CRltEpsilon.
  destruct (Z.le_gt_cases i 0).
  - (* i <= 0 *)
    clear H4. apply CRltForget.
    apply (CRlt_le_trans _ (CRabs _ (f a) + 1)).
    apply (CRplus_lt_reg_r (-CRabs _ (f a))).
    rewrite (CRplus_comm (CRabs _ (f a))), CRplus_assoc.
    rewrite CRplus_opp_r, CRplus_0_r.
    apply (CRle_lt_trans _ _ _ (CRabs_triang_inv _ _)).
    apply (H _ _ (CRzero_lt_one R)).
    rewrite CRabs_right. apply (CRmult_lt_reg_r (CR_of_Q R 2)).
    apply CR_of_Q_pos; reflexivity.
    apply (CRlt_le_trans _ _ _ H5). rewrite CRmult_comm.
    apply CRmult_le_compat_l. apply CRlt_asym, (fst fUC).
    rewrite <- (CRplus_0_l (CR_of_Q R 2)), <- CRplus_assoc.
    apply CRplus_le_compat. 2: apply CRle_refl.
    rewrite CRplus_0_r. rewrite <- CR_of_Q_zero. apply CR_of_Q_le.
    unfold Qle,Qnum,Qden. simpl. rewrite Z.mul_1_r. exact H3.
    apply CRle_minus. exact H1.
    rewrite (UniformContProper
               f fMod fUC _ (a + INR 0 * fMod 1 (CRzero_lt_one R) * CR_of_Q R (1#2))).
    apply CRplus_le_compat. 2: apply CRle_refl.
    apply maxouSpec, le_0_n. unfold INR, Z.of_nat.
    rewrite CR_of_Q_zero.
    rewrite CRmult_0_l, CRmult_0_l, CRplus_0_r. reflexivity.
  - (* 0 < i *)
    apply CRltForget.
    apply (CRlt_le_trans
             _ (CRabs _ (f (a + CR_of_Q R (i#1) * fMod 1 (CRzero_lt_one R) * CR_of_Q R (1#2))) + 1)).
    + apply (CRplus_lt_reg_l _
               (-CRabs _ (f (a + CR_of_Q R (i#1)
                                   * fMod 1 (CRzero_lt_one R) * CR_of_Q R (1#2))))).
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l, CRplus_comm.
      apply (CRle_lt_trans _ _ _ (CRabs_triang_inv _ _)).
      apply (H _ _ (CRzero_lt_one R)).
      rewrite CRabs_right.
      apply (CRplus_lt_reg_r
               (a + CR_of_Q R (i#1) * (fMod 1 (CRzero_lt_one R) * CR_of_Q R (1#2)))).
      unfold CRminus.
      rewrite CRplus_assoc, <- CRmult_assoc, CRplus_opp_l, CRplus_0_r.
      rewrite CRplus_comm. apply (CRplus_lt_reg_l _ (-a)).
      do 2 rewrite <- CRplus_assoc. rewrite CRplus_opp_l, CRplus_0_l.
      rewrite CRplus_comm. apply (CRmult_lt_reg_r (CR_of_Q R 2)).
      apply CR_of_Q_pos; reflexivity.
      apply (CRlt_le_trans _ _ _ H5).
      do 2 rewrite CRmult_plus_distr_r. apply CRplus_le_compat.
      2: rewrite CRmult_comm; apply CRle_refl.
      do 2 rewrite CRmult_assoc. rewrite <- CR_of_Q_mult.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_r, CRmult_comm. apply CRle_refl. reflexivity.
      unfold CRminus. rewrite CRopp_plus_distr, <- CRplus_assoc.
      apply (CRle_minus (CR_of_Q R (i # 1) * fMod 1 (CRzero_lt_one R) * CR_of_Q R (1 # 2))
                        (x - a)).
      apply CRlt_asym, (CRmult_lt_reg_r (CR_of_Q R 2)).
      apply CR_of_Q_pos; reflexivity.
      do 2 rewrite CRmult_assoc. rewrite <- CR_of_Q_mult.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q.
      rewrite CR_of_Q_one, CRmult_1_r. exact H4. reflexivity.
    + clear H5. apply CRplus_le_compat. 2: apply CRle_refl.
      unfold INR in maxouSpec.
      destruct i. exfalso; inversion H3. 2: exfalso; inversion H3.
      specialize (maxouSpec (Pos.to_nat p) k).
      rewrite positive_nat_Z in maxouSpec. apply maxouSpec.
      apply (CRmult_lt_compat_r (fMod 1 (CRzero_lt_one R))) in kmaj.
      rewrite CRmult_assoc, CRinv_l, CRmult_1_r in kmaj.
      2: apply (fst fUC).
      assert ((x-a)*CR_of_Q R 2 <= (b-a)*CR_of_Q R 2).
      { apply CRmult_le_compat_r.
        rewrite <- CR_of_Q_zero. apply CR_of_Q_le; discriminate.
        apply CRplus_le_compat. exact H2. apply CRle_refl. }
      apply (CRlt_le_trans _ _ _ H4) in H5. clear H4.
      apply (CRlt_trans _ _ _ H5) in kmaj. clear H5.
      apply CRmult_lt_reg_r in kmaj. 2: apply (fst fUC).
      destruct (Q_dec (Z.pos p # 1) (Z.of_nat k # 1)). destruct s.
      unfold Qlt, Qnum, Qden in q.
      apply le_S_n. apply (le_trans _ k).
      apply Nat2Z.inj_lt. rewrite positive_nat_Z.
      do 2 rewrite Z.mul_1_r in q. exact q.
      apply le_S, le_refl. exfalso. apply (CR_of_Q_lt R) in q.
      exact (CRlt_asym _ _ q kmaj). exfalso.
      rewrite q in kmaj. exact (CRlt_asym _ _ kmaj kmaj).
Qed.

Definition CSUC_bounded {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R)
           (a b : CRcarrier R) (fMod : forall eps:CRcarrier R, 0 < eps -> CRcarrier R)
           (fCSUC : CSUC f a b fMod)
  : a <= b -> { B : CRcarrier R & forall x:CRcarrier R, CRabs _ (f x) < B }.
Proof.
  intros. destruct fCSUC as [H0 H1].
  destruct (UC_bounded f (a-1) (b+1) fMod H0) as [B Bmaj].
  apply Rminus_plus_one_lower. apply H. exists B.
  assert (0 < B) as Bpos.
  { specialize (Bmaj a). apply (CRle_lt_trans _ (CRabs _ (f a))).
    apply CRabs_pos. apply Bmaj.
    apply CRlt_asym, Rminus_pos_lower. apply CRzero_lt_one.
    apply (CRle_trans _ b _ H).
    apply CRlt_asym, Rplus_pos_higher. apply CRzero_lt_one. }
  intros. destruct (CRltLinear R).
  destruct (s (a-1) x a (Rminus_pos_lower a 1 (CRzero_lt_one R))).
  - destruct (s b x (b+1) (Rplus_pos_higher b 1 (CRzero_lt_one R))).
    rewrite H1. rewrite CRabs_right. apply Bpos.
    apply CRle_refl.
    right. exact c0. apply Bmaj. apply CRlt_asym, c.
    apply CRlt_asym, c0.
  - rewrite H1. rewrite CRabs_right. apply Bpos.
    apply CRle_refl. left. exact c.
Qed.

(* Used to zoom in subdomains in the proof of Icontinuous below *)
Lemma CSUC_func_mult_stable
  : forall {R : ConstructiveReals} (f g : CRcarrier R -> CRcarrier R) (a b : CRcarrier R)
      (modF modG : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    CSUC f a b modF
    -> a <= b
    -> UniformCont g modG
    -> { modFG : forall x:CRcarrier R, 0 < x -> CRcarrier R
      & CSUC (fun x => f x * g x) a b modFG }.
Proof.
  intros.
  destruct (CSUC_bounded f a b modF H H0)
    as [Bf majf].
  destruct H. assert (0 < Bf) as Bfpos.
  { specialize (majf a). apply (CRle_lt_trans _ (CRabs _ (f a))).
    apply CRabs_pos. apply majf. }
  destruct (UC_bounded g (a-1) (b+1) modG H1 (Rminus_plus_one_lower a b H0))
    as [Bg majg].
  assert (0 < Bg) as Bgpos.
  { specialize (majg a). apply (CRle_lt_trans _ (CRabs _ (g a))).
    apply CRabs_pos. apply majg.
    apply CRlt_asym, Rminus_pos_lower. apply CRzero_lt_one.
    apply (CRle_trans _ b _ H0).
    apply CRlt_asym, Rplus_pos_higher. apply CRzero_lt_one. }
  assert (forall eps:CRcarrier R, 0 < eps -> 0 < eps * CR_of_Q R (1#2) * (CRinv R Bg (inr Bgpos))).
  { intros. apply CRmult_lt_0_compat.
    apply CRmult_lt_0_compat. exact H.
    apply CR_of_Q_pos; reflexivity.
    apply CRinv_0_lt_compat, Bgpos. }
  assert (forall eps:CRcarrier R, 0 < eps -> 0 < eps * CR_of_Q R (1#2) * (CRinv R Bf (inr Bfpos))).
  { intros. apply CRmult_lt_0_compat.
    apply CRmult_lt_0_compat. exact H2.
    apply CR_of_Q_pos; reflexivity.
    apply CRinv_0_lt_compat, Bfpos. }
  exists (fun eps epsPos => CRmin (modF (eps * CR_of_Q R (1#2) * CRinv R Bg (inr Bgpos))
                                    (H eps epsPos))
                              (modG (eps * CR_of_Q R (1#2) * CRinv R Bf (inr Bfpos))
                                    (H2 eps epsPos))).
  split. split.
  - intros. apply CRmin_lt. apply (fst u). apply (fst H1).
  - intros. destruct (CRltLinear R).
    destruct (s (a-1) x a (Rminus_pos_lower a 1 (CRzero_lt_one R))).
    + destruct (s b x (b+1) (Rplus_pos_higher b 1 (CRzero_lt_one R))).
      (* x is out to the right. *)
      destruct (s (a-1) y a (Rminus_pos_lower a 1 (CRzero_lt_one R))).
      destruct (s b y (b+1) (Rplus_pos_higher b 1 (CRzero_lt_one R))).
      rewrite c,c. do 2 rewrite CRmult_0_l.
      unfold CRminus. rewrite CRplus_0_l. rewrite CRopp_0.
      rewrite CRabs_right. apply epsPos.
      apply CRle_refl. right. exact c3. right. exact c1.
      (* y is inside *)
      specialize (c x (inr c1)).
      setoid_replace (f x * g x - f y * g y) with ((f x - f y) * g y).
      2: rewrite c.
      rewrite CRabs_mult. rewrite CRmult_comm.
      apply (CRle_lt_trans _ (Bg * CRabs _ (f x - f y))).
      apply CRmult_le_compat_r. apply CRabs_pos.
      apply CRlt_asym, majg.
      apply CRlt_asym, c2. apply CRlt_asym, c3.
      apply (CRlt_le_trans _ (Bg * (eps * CR_of_Q R (1#2) * CRinv R Bg (inr Bgpos)))).
      apply CRmult_lt_compat_l. apply Bgpos. destruct u.
      apply (c5 _ _ _ (H _ epsPos)).
      apply (CRlt_le_trans _ _ _ H3). apply CRmin_l.
      rewrite CRmult_comm, CRmult_assoc, CRinv_l, CRmult_1_r.
      rewrite <- (CRmult_1_r eps), CRmult_assoc.
      apply CRmult_le_compat_l. apply CRlt_asym, epsPos.
      rewrite CRmult_1_l, <- CR_of_Q_one. apply CR_of_Q_le; discriminate.

      unfold CRminus. rewrite CRmult_0_l, CRplus_0_l, CRplus_0_l.
      apply CRopp_mult_distr_l.
      (* y < a *)
      rewrite c, c.
      do 2 rewrite CRmult_0_l.
      unfold CRminus. rewrite CRplus_0_l. rewrite CRopp_0.
      rewrite CRabs_right. apply epsPos.
      apply CRle_refl. left. exact c2. right. exact c1.

      (* x is inside *)
      setoid_replace (f x * g x - f y * g y)
        with (g x * (f x - f y) + f y *(g x - g y)).
      apply (CRle_lt_trans _ _ _ (CRabs_triang _ _)).
      setoid_replace eps
        with (eps*CR_of_Q R (1#2) + eps*CR_of_Q R (1#2)).
      apply CRplus_le_lt_compat. apply CRlt_asym.
      * (* delta f *) rewrite CRabs_mult.
        apply (CRle_lt_trans _ (Bg * CRabs _ (f x - f y))).
        apply CRmult_le_compat_r. apply CRabs_pos.
        apply CRlt_asym, majg.
        apply CRlt_asym, c0. apply CRlt_asym, c1.
        apply (CRlt_le_trans
                 _ (Bg * (eps * CR_of_Q R (1#2) * CRinv R Bg (inr Bgpos)))).
        apply CRmult_lt_compat_l. apply Bgpos. destruct u.
        apply (c3 _ _ _ (H _ epsPos)).
        apply (CRlt_le_trans _ _ _ H3). apply CRmin_l.
        rewrite CRmult_comm, CRmult_assoc, CRinv_l.
        rewrite CRmult_1_r. apply CRle_refl.
      * (* delta g *) rewrite CRabs_mult.
        apply (CRle_lt_trans _ (Bf * CRabs _ (g x - g y))).
        apply CRmult_le_compat_r. apply CRabs_pos.
        apply CRlt_asym, majf.
        apply (CRlt_le_trans
                 _ (Bf * (eps *CR_of_Q R (1#2) * CRinv R Bf (inr Bfpos)))).
        apply CRmult_lt_compat_l. apply Bfpos. destruct H1.
        apply (c3 _ _ _ (H2 _ epsPos)).
        apply (CRlt_le_trans _ _ _ H3). apply CRmin_r.
        rewrite CRmult_comm, CRmult_assoc, CRinv_l.
        rewrite CRmult_1_r. apply CRle_refl.
      * rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus.
        setoid_replace ((1#2) + (1#2))%Q with 1%Q.
        rewrite CR_of_Q_one, CRmult_1_r. reflexivity. reflexivity.
      * unfold CRminus. do 2 rewrite CRmult_plus_distr_l.
        rewrite CRplus_assoc. apply CRplus_morph.
        apply CRmult_comm. rewrite <- CRplus_assoc, (CRmult_comm (g x)).
        rewrite <- CRmult_plus_distr_r, CRplus_opp_l, CRmult_0_l.
        rewrite CRplus_0_l, CRopp_mult_distr_r. reflexivity.
    + (* x is out to the left. *)
      destruct (s (a-1) y a (Rminus_pos_lower a 1 (CRzero_lt_one R))).
      destruct (s b y (b+1) (Rplus_pos_higher b 1 (CRzero_lt_one R))).
      * rewrite c,c. do 2 rewrite CRmult_0_l.
        unfold CRminus. rewrite CRplus_0_l. rewrite CRopp_0.
        rewrite CRabs_right. apply epsPos.
        apply CRle_refl. right. exact c2. left. exact c0.
      * (* y is inside *)
        specialize (c x (inl c0)).
        setoid_replace (f x * g x - f y * g y)
          with ((f x - f y) * g y).
        2: rewrite c.
        rewrite CRabs_mult. rewrite CRmult_comm.
        apply (CRle_lt_trans _ (Bg * CRabs _ (f x - f y))).
        apply CRmult_le_compat_r. apply CRabs_pos.
        apply CRlt_asym, majg.
        apply CRlt_asym, c1. apply CRlt_asym, c2.
        apply (CRlt_le_trans
                 _ (Bg * (eps * CR_of_Q R (1#2) * CRinv R Bg (inr Bgpos)))).
        apply CRmult_lt_compat_l. apply Bgpos. destruct u.
        apply (c4 _ _ _ (H _ epsPos)).
        apply (CRlt_le_trans _ _ _ H3). apply CRmin_l.
        rewrite CRmult_comm, CRmult_assoc, CRinv_l.
        rewrite CRmult_1_r.
        rewrite <- (CRmult_1_r eps), CRmult_assoc.
        apply CRmult_le_compat_l. apply CRlt_asym, epsPos.
        rewrite CRmult_1_l, <- CR_of_Q_one. apply CR_of_Q_le; discriminate.
        rewrite CRmult_0_l. unfold CRminus. do 2 rewrite CRplus_0_l.
        rewrite CRopp_mult_distr_l. reflexivity.
      * rewrite c,c. do 2 rewrite CRmult_0_l.
        unfold CRminus. rewrite CRplus_0_l. rewrite CRopp_0.
        rewrite CRabs_right. apply epsPos.
        apply CRle_refl. left. exact c1. left. exact c0.
  - intros. destruct H3. rewrite c, CRmult_0_l. reflexivity.
    left. exact c0. rewrite c, CRmult_0_l. reflexivity.
    right. exact c0.
Qed.

Lemma Rplus_lt_epsilon : forall {R : ConstructiveReals} (a b c d : CRcarrier R),
    (a + b) < (c + d)  ->  sum (a < c) (b < d).
Proof.
  intros. destruct (CRltLinear R). destruct (s (a+b) (a+d) (c+d) H).
  - right. apply CRplus_lt_reg_l in c0. exact c0.
  - left. apply CRplus_lt_reg_r in c0. exact c0.
Qed.

Lemma EnlargePointMajorationZero
  : forall {R : ConstructiveReals} (f : CRcarrier R -> CRcarrier R) (x : CRcarrier R)
      (modF : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    UniformCont f modF
    -> 0 < f x
    -> { eta : CRcarrier R & prod (0 < eta) (forall y:CRcarrier R, CRabs _ (x-y) < eta -> 0 < (f y)) }.
Proof.
  intros. destruct H as [H H1]. exists (modF (f x) H0).
  split.
  - apply H.
  - intros. specialize (H1 (f x) x y H0 H2).
    apply (CRle_lt_trans _ _ _ (CRle_abs _)) in H1.
    apply (CRplus_lt_reg_l _ (f x - f y)).
    rewrite CRplus_0_r. unfold CRminus.
    rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    exact H1.
Qed.

Lemma EnlargePointMajoration
  : forall {R : ConstructiveReals} (f g : CRcarrier R -> CRcarrier R) (x : CRcarrier R)
      (modF modG : forall x:CRcarrier R, 0 < x -> CRcarrier R),
    UniformCont f modF
    -> UniformCont g modG
    -> f x < g x
    -> { eta : CRcarrier R & prod (0 < eta) (forall y:CRcarrier R, CRabs _ (x-y) < eta -> f y < g y) }.
Proof.
  intros.
  pose proof (UC_scale f modF (-(1)) H).
  pose proof (UC_plus (fun x => -(1)*f x) g _ modG H2 H0).
  destruct (EnlargePointMajorationZero (fun t => -(1)*f t + g t) x _ H3).
  rewrite <- CRopp_mult_distr_l, CRopp_mult_distr_r. rewrite CRmult_1_l.
  apply (CRplus_lt_reg_l _ (f x)).
  rewrite <- CRplus_assoc, CRplus_opp_r.
  rewrite CRplus_0_l, CRplus_0_r. exact H1.
  exists x0. destruct p. split. exact c. intros.
  specialize (c0 y H4). apply (CRplus_lt_compat_l _ (f y)) in c0.
  rewrite CRplus_0_r in c0.
  setoid_replace (g y) with (f y + (- (1) * f y + g y)).
  exact c0. rewrite <- CRopp_mult_distr_l, CRmult_1_l.
  rewrite <- CRplus_assoc, CRplus_opp_r. rewrite CRplus_0_l. reflexivity.
Qed.
