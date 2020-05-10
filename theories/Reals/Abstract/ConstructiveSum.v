(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import QArith Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.

Local Open Scope ConstructiveReals.


(**
   Definition and properties of finite sums and powers.
*)

Fixpoint CRsum {R : ConstructiveReals}
         (f:nat -> CRcarrier R) (N:nat) : CRcarrier R :=
  match N with
    | O => f 0%nat
    | S i => CRsum f i + f (S i)
  end.

Fixpoint CRpow {R : ConstructiveReals} (r:CRcarrier R) (n:nat) : CRcarrier R :=
  match n with
    | O => 1
    | S n => r * (CRpow r n)
  end.

Lemma CRsum_eq :
  forall {R : ConstructiveReals} (An Bn:nat -> CRcarrier R) (N:nat),
    (forall i:nat, (i <= N)%nat -> An i == Bn i) ->
    CRsum An N == CRsum Bn N.
Proof.
  induction N.
  - intros. exact (H O (le_refl _)).
  - intros. simpl. apply CRplus_morph. apply IHN.
    intros. apply H. apply (le_trans _ N _ H0), le_S, le_refl.
    apply H, le_refl.
Qed.

Lemma sum_eq_R0 : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (n : nat),
    (forall k:nat, un k == 0)
    -> CRsum un n == 0.
Proof.
  induction n.
  - intros. apply H.
  - intros. simpl. rewrite IHn. rewrite H. apply CRplus_0_l. exact H.
Qed.

Definition INR {R : ConstructiveReals} (n : nat) : CRcarrier R
  := CR_of_Q R (Z.of_nat n # 1).

Lemma sum_const : forall {R : ConstructiveReals} (a : CRcarrier R) (n : nat),
    CRsum (fun _ => a) n == a * INR (S n).
Proof.
  induction n.
  - unfold INR. simpl. rewrite CRmult_1_r. reflexivity.
  - simpl. rewrite IHn. unfold INR.
    replace (Z.of_nat (S (S n))) with (Z.of_nat (S n) + 1)%Z.
    rewrite <- Qinv_plus_distr, CR_of_Q_plus, CRmult_plus_distr_l.
    apply CRplus_morph. reflexivity. rewrite CRmult_1_r. reflexivity.
    replace 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add.
    apply f_equal. rewrite Nat.add_comm. reflexivity. reflexivity.
Qed.

Lemma multiTriangleIneg : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (n : nat),
    CRabs R (CRsum u n) <= CRsum (fun k => CRabs R (u k)) n.
Proof.
  induction n.
  - apply CRle_refl.
  - simpl. apply (CRle_trans _ (CRabs R (CRsum u n) + CRabs R (u (S n)))).
    apply CRabs_triang. apply CRplus_le_compat. apply IHn.
    apply CRle_refl.
Qed.

Lemma sum_assoc : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (n p : nat),
    CRsum u (S n + p)
    == CRsum u n + CRsum (fun k => u (S n + k)%nat) p.
Proof.
  induction p.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite (Radd_assoc (CRisRing R)). apply CRplus_morph.
    rewrite Nat.add_succ_r.
    rewrite (CRsum_eq (fun k : nat => u (S (n + k))) (fun k : nat => u (S n + k)%nat)).
    rewrite <- IHp. reflexivity. intros. reflexivity. reflexivity.
Qed.

Lemma sum_Rle : forall {R : ConstructiveReals} (un vn : nat -> CRcarrier R) (n : nat),
    (forall k, le k n -> un k <= vn k)
    -> CRsum un n <= CRsum vn n.
Proof.
  induction n.
  - intros. apply H. apply le_refl.
  - intros. simpl. apply CRplus_le_compat. apply IHn.
    intros. apply H. apply (le_trans _ n _ H0). apply le_S, le_refl.
    apply H. apply le_refl.
Qed.

Lemma Abs_sum_maj : forall {R : ConstructiveReals} (un vn : nat -> CRcarrier R),
    (forall n:nat, CRabs R (un n) <= (vn n))
    -> forall n p:nat, (CRabs R (CRsum un n - CRsum un p) <=
              CRsum vn (Init.Nat.max n p) - CRsum vn (Init.Nat.min n p)).
Proof.
  intros. destruct (le_lt_dec n p).
  - destruct (Nat.le_exists_sub n p) as [k [maj _]]. assumption.
    subst p. rewrite max_r. rewrite min_l.
    setoid_replace (CRsum un n - CRsum un (k + n))
      with (-(CRsum un (k + n) - CRsum un n)).
    rewrite CRabs_opp.
    destruct k. simpl. unfold CRminus. rewrite CRplus_opp_r.
    rewrite CRplus_opp_r. rewrite CRabs_right.
    apply CRle_refl. apply CRle_refl.
    replace (S k + n)%nat with (S n + k)%nat.
    unfold CRminus. rewrite sum_assoc. rewrite sum_assoc.
    rewrite CRplus_comm.
    rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
    rewrite CRplus_0_l. rewrite CRplus_comm.
    rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
    rewrite CRplus_0_l.
    apply (CRle_trans _ (CRsum (fun k0 : nat => CRabs R (un (S n + k0)%nat)) k)).
    apply multiTriangleIneg. apply sum_Rle. intros.
    apply H. rewrite Nat.add_comm, Nat.add_succ_r. reflexivity.
    unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive, CRplus_comm.
    reflexivity. assumption. assumption.
  - destruct (Nat.le_exists_sub p n) as [k [maj _]]. unfold lt in l.
    apply (le_trans p (S p)). apply le_S. apply le_refl. assumption.
    subst n. rewrite max_l. rewrite min_r.
    destruct k. simpl. unfold CRminus. rewrite CRplus_opp_r.
    rewrite CRplus_opp_r. rewrite CRabs_right. apply CRle_refl.
    apply CRle_refl.
    replace (S k + p)%nat with (S p + k)%nat. unfold CRminus.
    rewrite sum_assoc. rewrite sum_assoc.
    rewrite CRplus_comm.
    rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
    rewrite CRplus_0_l. rewrite CRplus_comm.
    rewrite <- CRplus_assoc. rewrite CRplus_opp_l.
    rewrite CRplus_0_l.
    apply (CRle_trans _ (CRsum (fun k0 : nat => CRabs R (un (S p + k0)%nat)) k)).
    apply multiTriangleIneg. apply sum_Rle. intros.
    apply H. rewrite Nat.add_comm, Nat.add_succ_r. reflexivity.
    apply (le_trans p (S p)). apply le_S. apply le_refl. assumption.
    apply (le_trans p (S p)). apply le_S. apply le_refl. assumption.
Qed.

Lemma cond_pos_sum : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (n : nat),
    (forall k, 0 <= un k)
    -> 0 <= CRsum un n.
Proof.
  induction n.
  - intros. apply H.
  - intros. simpl. rewrite <- CRplus_0_r.
    apply CRplus_le_compat. apply IHn, H. apply H.
Qed.

Lemma pos_sum_more : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
                       (n p : nat),
    (forall k:nat, 0 <= u k)
    -> le n p -> CRsum u n <= CRsum u p.
Proof.
  intros. destruct (Nat.le_exists_sub n p H0). destruct H1. subst p.
  rewrite plus_comm.
  destruct x. rewrite plus_0_r. apply CRle_refl. rewrite Nat.add_succ_r.
  replace (S (n + x)) with (S n + x)%nat. rewrite sum_assoc.
  rewrite <- CRplus_0_r, CRplus_assoc.
  apply CRplus_le_compat_l. rewrite CRplus_0_l.
  apply cond_pos_sum.
  intros. apply H. auto.
Qed.

Lemma sum_opp : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (n : nat),
    CRsum (fun k => - un k) n == - CRsum un n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite CRopp_plus_distr. reflexivity.
Qed.

Lemma sum_scale : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (a : CRcarrier R) (n : nat),
    CRsum (fun k : nat => u k * a) n == CRsum u n * a.
Proof.
  induction n.
  - simpl. rewrite (Rmul_comm (CRisRing R)). reflexivity.
  - simpl. rewrite IHn. rewrite CRmult_plus_distr_r.
    apply CRplus_morph. reflexivity.
    rewrite (Rmul_comm (CRisRing R)). reflexivity.
Qed.

Lemma sum_plus : forall {R : ConstructiveReals} (u v : nat -> CRcarrier R) (n : nat),
    CRsum (fun n0 : nat => u n0 + v n0) n == CRsum u n + CRsum v n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. do 2 rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity. rewrite CRplus_comm, CRplus_assoc.
    apply CRplus_morph. reflexivity. apply CRplus_comm.
Qed.

Lemma decomp_sum :
  forall {R : ConstructiveReals} (An:nat -> CRcarrier R) (N:nat),
    (0 < N)%nat ->
    CRsum An N == An 0%nat + CRsum (fun i:nat => An (S i)) (pred N).
Proof.
  induction N.
  - intros. exfalso. inversion H.
  - intros _. destruct N. simpl. reflexivity. simpl.
    rewrite IHN. rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity. reflexivity.
    apply le_n_S, le_0_n.
Qed.

Lemma reverse_sum : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (n : nat),
    CRsum u n == CRsum (fun k => u (n-k)%nat) n.
Proof.
  induction n.
  - intros. reflexivity.
  - rewrite (decomp_sum (fun k : nat => u (S n - k)%nat)). simpl.
    rewrite CRplus_comm. apply CRplus_morph. reflexivity. assumption.
    unfold lt. apply le_n_S. apply le_0_n.
Qed.

Lemma Rplus_le_pos : forall {R : ConstructiveReals} (a b : CRcarrier R),
    0 <= b -> a <= a + b.
Proof.
  intros. rewrite <- (CRplus_0_r a). rewrite CRplus_assoc.
  apply CRplus_le_compat_l. rewrite CRplus_0_l. assumption.
Qed.

Lemma selectOneInSum : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (n i : nat),
    le i n
    -> (forall k:nat, 0 <= u k)
    -> u i <= CRsum u n.
Proof.
  induction n.
  - intros. inversion H. subst i. apply CRle_refl.
  - intros. apply Nat.le_succ_r in H. destruct H.
    apply (CRle_trans _ (CRsum u n)). apply IHn. assumption. assumption.
    simpl. apply Rplus_le_pos. apply H0.
    subst i. simpl. rewrite CRplus_comm. apply Rplus_le_pos.
    apply cond_pos_sum. intros. apply H0.
Qed.

Lemma splitSum : forall {R : ConstructiveReals} (un : nat -> CRcarrier R)
                        (filter : nat -> bool) (n : nat),
    CRsum un n
    == CRsum (fun i => if filter i then un i else 0) n
       + CRsum (fun i => if filter i then 0 else un i) n.
Proof.
  induction n.
  - simpl. destruct (filter O). symmetry; apply CRplus_0_r.
    symmetry. apply CRplus_0_l.
  - simpl. rewrite IHn. clear IHn. destruct (filter (S n)).
    do 2 rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    rewrite CRplus_comm. apply CRplus_morph. reflexivity. rewrite CRplus_0_r.
    reflexivity. rewrite CRplus_0_r. rewrite CRplus_assoc. reflexivity.
Qed.


(* Power *)

Lemma pow_R1_Rle : forall {R : ConstructiveReals} (x : CRcarrier R) (n : nat),
    1 <= x
    -> 1 <= CRpow x n.
Proof.
  induction n.
  - intros. apply CRle_refl.
  - intros. simpl. apply (CRle_trans _ (x * 1)).
    rewrite CRmult_1_r. exact H.
    apply CRmult_le_compat_l_half. apply (CRlt_le_trans _ 1).
    apply CRzero_lt_one. exact H.
    apply IHn. exact H.
Qed.

Lemma pow_le : forall {R : ConstructiveReals} (x : CRcarrier R) (n : nat),
    0 <= x
    -> 0 <= CRpow x n.
Proof.
  induction n.
  - intros. apply CRlt_asym, CRzero_lt_one.
  - intros. simpl. apply CRmult_le_0_compat.
    exact H. apply IHn. exact H.
Qed.

Lemma pow_lt : forall {R : ConstructiveReals} (x : CRcarrier R) (n : nat),
    0 < x
    -> 0 < CRpow x n.
Proof.
  induction n.
  - intros. apply CRzero_lt_one.
  - intros. simpl. apply CRmult_lt_0_compat. exact H.
    apply IHn. exact H.
Qed.

Lemma pow_mult : forall {R : ConstructiveReals} (x y : CRcarrier R) (n:nat),
    CRpow x n * CRpow y n == CRpow (x*y) n.
Proof.
  induction n.
  - simpl. rewrite CRmult_1_r. reflexivity.
  - simpl. rewrite <- IHn. do 2 rewrite <- (Rmul_assoc (CRisRing R)).
    apply CRmult_morph. reflexivity.
    rewrite <- (Rmul_comm (CRisRing R)). rewrite <- (Rmul_assoc (CRisRing R)).
    apply CRmult_morph. reflexivity.
    rewrite <- (Rmul_comm (CRisRing R)). reflexivity.
Qed.

Lemma pow_one : forall {R : ConstructiveReals} (n:nat),
    @CRpow R 1 n == 1.
Proof.
  induction n. reflexivity.
  transitivity (CRmult R 1 (CRpow 1 n)). reflexivity.
  rewrite IHn. rewrite CRmult_1_r. reflexivity.
Qed.

Lemma pow_proper : forall {R : ConstructiveReals} (x y : CRcarrier R) (n : nat),
    x == y -> CRpow x n == CRpow y n.
Proof.
  induction n.
  - intros. reflexivity.
  - intros. simpl. rewrite IHn, H. reflexivity. exact H.
Qed.

Lemma pow_inv : forall {R : ConstructiveReals} (x : CRcarrier R) (xPos : 0 < x) (n : nat),
    CRpow (CRinv R x (inr xPos)) n
    == CRinv R (CRpow x n) (inr (pow_lt x n xPos)).
Proof.
  induction n.
  - rewrite CRinv_1. reflexivity.
  - transitivity (CRinv R x (inr xPos) * CRpow (CRinv R x (inr xPos)) n).
    reflexivity. rewrite IHn.
    assert (0 < x * CRpow x n).
    { apply CRmult_lt_0_compat. exact xPos. apply pow_lt, xPos. }
    rewrite <- (CRinv_mult_distr _ _ _ _ (inr H)).
    apply CRinv_morph. reflexivity.
Qed.

Lemma pow_plus_distr : forall {R : ConstructiveReals} (x : CRcarrier R) (n p:nat),
    CRpow x n * CRpow x p == CRpow x (n+p).
Proof.
  induction n.
  - intros. simpl. rewrite CRmult_1_l. reflexivity.
  - intros. simpl. rewrite CRmult_assoc. apply CRmult_morph.
    reflexivity. apply IHn.
Qed.
