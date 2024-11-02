(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Znat.
Require Import QArith Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveRealsMorphisms.
Require Import ConstructiveAbs.
Require Import ConstructiveLimits.
Require Import ConstructiveSum.

Local Open Scope ConstructiveReals.


(**
   Definition and properties of powers.

   WARNING: this file is experimental and likely to change in future releases.
*)

Fixpoint CRpow {R : ConstructiveReals} (r:CRcarrier R) (n:nat) : CRcarrier R :=
  match n with
    | O => 1
    | S n => r * (CRpow r n)
  end.

Lemma CRpow_ge_one : forall {R : ConstructiveReals} (x : CRcarrier R) (n : nat),
    1 <= x
    -> 1 <= CRpow x n.
Proof.
  induction n.
  - intros. apply CRle_refl.
  - intros. simpl. apply (CRle_trans _ (x * 1)).
    + rewrite CRmult_1_r. exact H.
    + apply CRmult_le_compat_l_half.
      * apply (CRlt_le_trans _ 1).
        -- apply CRzero_lt_one.
        -- exact H.
      * apply IHn. exact H.
Qed.

Lemma CRpow_ge_zero : forall {R : ConstructiveReals} (x : CRcarrier R) (n : nat),
    0 <= x
    -> 0 <= CRpow x n.
Proof.
  induction n.
  - intros. apply CRlt_asym, CRzero_lt_one.
  - intros. simpl. apply CRmult_le_0_compat.
    + exact H.
    + apply IHn. exact H.
Qed.

Lemma CRpow_gt_zero : forall {R : ConstructiveReals} (x : CRcarrier R) (n : nat),
    0 < x
    -> 0 < CRpow x n.
Proof.
  induction n.
  - intros. apply CRzero_lt_one.
  - intros. simpl. apply CRmult_lt_0_compat.
    + exact H.
    + apply IHn. exact H.
Qed.

Lemma CRpow_mult : forall {R : ConstructiveReals} (x y : CRcarrier R) (n:nat),
    CRpow x n * CRpow y n == CRpow (x*y) n.
Proof.
  induction n.
  - simpl. rewrite CRmult_1_r. reflexivity.
  - simpl. rewrite <- IHn. do 2 rewrite <- (Rmul_assoc (CRisRing R)).
    apply CRmult_morph.
    + reflexivity.
    + rewrite <- (Rmul_comm (CRisRing R)). rewrite <- (Rmul_assoc (CRisRing R)).
      apply CRmult_morph.
      * reflexivity.
      * rewrite <- (Rmul_comm (CRisRing R)). reflexivity.
Qed.

Lemma CRpow_one : forall {R : ConstructiveReals} (n:nat),
    @CRpow R 1 n == 1.
Proof.
  induction n.
  - reflexivity.
  - transitivity (CRmult R 1 (CRpow 1 n)).
    + reflexivity.
    + rewrite IHn. rewrite CRmult_1_r. reflexivity.
Qed.

Lemma CRpow_proper : forall {R : ConstructiveReals} (x y : CRcarrier R) (n : nat),
    x == y -> CRpow x n == CRpow y n.
Proof.
  induction n.
  - intros. reflexivity.
  - intros. simpl. rewrite IHn, H. + reflexivity. + exact H.
Qed.

Lemma CRpow_inv : forall {R : ConstructiveReals} (x : CRcarrier R) (xPos : 0 < x) (n : nat),
    CRpow (CRinv R x (inr xPos)) n
    == CRinv R (CRpow x n) (inr (CRpow_gt_zero x n xPos)).
Proof.
  induction n.
  - rewrite CRinv_1. reflexivity.
  - transitivity (CRinv R x (inr xPos) * CRpow (CRinv R x (inr xPos)) n).
    + reflexivity.
    + rewrite IHn.
      assert (0 < x * CRpow x n).
      { apply CRmult_lt_0_compat.
        * exact xPos.
        * apply CRpow_gt_zero, xPos. }
      rewrite <- (CRinv_mult_distr _ _ _ _ (inr H)).
      apply CRinv_morph. reflexivity.
Qed.

Lemma CRpow_plus_distr : forall {R : ConstructiveReals} (x : CRcarrier R) (n p:nat),
    CRpow x n * CRpow x p == CRpow x (n+p).
Proof.
  induction n.
  - intros. simpl. rewrite CRmult_1_l. reflexivity.
  - intros. simpl. rewrite CRmult_assoc. apply CRmult_morph.
    + reflexivity. + apply IHn.
Qed.

Lemma CR_double : forall {R : ConstructiveReals} (x:CRcarrier R),
    CR_of_Q R 2 * x == x + x.
Proof.
  intros R x. rewrite (CR_of_Q_morph R 2 (1+1)).
  2: reflexivity. rewrite CR_of_Q_plus.
  rewrite CRmult_plus_distr_r, CRmult_1_l. reflexivity.
Qed.

Lemma GeoCvZero : forall {R : ConstructiveReals},
    CR_cv R (fun n:nat => CRpow (CR_of_Q R (1#2)) n) 0.
Proof.
  intro R. assert (forall n:nat, INR n < CRpow (CR_of_Q R 2) n).
  { induction n.
    - unfold INR; simpl.
      apply CRzero_lt_one.
    - unfold INR. fold (1+n)%nat.
      rewrite Nat2Z.inj_add.
      rewrite (CR_of_Q_morph R _ ((Z.of_nat 1 # 1) + (Z.of_nat n #1))).
      2: symmetry; apply Qinv_plus_distr.
      rewrite CR_of_Q_plus.
      replace (CRpow (CR_of_Q R 2) (1 + n))
        with (CR_of_Q R 2 * CRpow (CR_of_Q R 2) n).
      2: reflexivity. rewrite CR_double.
      apply CRplus_le_lt_compat.
      2: exact IHn. simpl.
      apply CRpow_ge_one. apply CR_of_Q_le. discriminate. }
  intros p. exists (Pos.to_nat p). intros.
  unfold CRminus. rewrite CRopp_0. rewrite CRplus_0_r.
  rewrite CRabs_right.
  2: apply CRpow_ge_zero; apply CR_of_Q_le; discriminate.
  apply CRlt_asym.
  apply (CRmult_lt_reg_l (CR_of_Q R (Z.pos p # 1))).
  - apply CR_of_Q_lt. reflexivity.
  - rewrite <- CR_of_Q_mult.
    rewrite (CR_of_Q_morph R ((Z.pos p # 1) * (1 # p)) 1).
    2: unfold Qmult, Qeq, Qnum, Qden; ring_simplify; reflexivity.
    apply (CRmult_lt_reg_r (CRpow (CR_of_Q R 2) i)).
    + apply CRpow_gt_zero.
      apply CR_of_Q_lt. reflexivity.
    + rewrite CRmult_assoc. rewrite CRpow_mult.
      rewrite (CRpow_proper (CR_of_Q R (1 # 2) * CR_of_Q R 2) 1), CRpow_one.
      * rewrite CRmult_1_r, CRmult_1_l.
        apply (CRle_lt_trans _ (INR i)). 2: exact (H i). clear H.
        apply CR_of_Q_le. unfold Qle,Qnum,Qden.
        do 2 rewrite Z.mul_1_r.
        rewrite <- positive_nat_Z. apply Nat2Z.inj_le, H0.
      * rewrite <- CR_of_Q_mult. setoid_replace ((1#2)*2)%Q with 1%Q.
        -- reflexivity.
        -- reflexivity.
Qed.

Lemma GeoFiniteSum : forall {R : ConstructiveReals} (n:nat),
    CRsum (CRpow (CR_of_Q R (1#2))) n == CR_of_Q R 2 - CRpow (CR_of_Q R (1#2)) n.
Proof.
  induction n.
  - unfold CRsum, CRpow. simpl (1%ConstructiveReals).
    unfold CRminus. rewrite (CR_of_Q_plus R 1 1).
    rewrite CRplus_assoc.
    rewrite CRplus_opp_r, CRplus_0_r. reflexivity.
  - setoid_replace (CRsum (CRpow (CR_of_Q R (1 # 2))) (S n))
      with (CRsum (CRpow (CR_of_Q R (1 # 2))) n + CRpow (CR_of_Q R (1 # 2)) (S n)).
    2: reflexivity.
    rewrite IHn. clear IHn. unfold CRminus.
    rewrite CRplus_assoc. apply CRplus_morph.
    + reflexivity.
    + apply (CRplus_eq_reg_l
               (CRpow (CR_of_Q R (1 # 2)) n + CRpow (CR_of_Q R (1 # 2)) (S n))).
      rewrite (CRplus_assoc _ _ (-CRpow (CR_of_Q R (1 # 2)) (S n))),
        CRplus_opp_r, CRplus_0_r.
      rewrite (CRplus_comm (CRpow (CR_of_Q R (1 # 2)) n)), CRplus_assoc.
      rewrite <- (CRplus_assoc (CRpow (CR_of_Q R (1 # 2)) n)), CRplus_opp_r,
        CRplus_0_l, <- CR_double.
      setoid_replace (CRpow (CR_of_Q R (1 # 2)) (S n))
        with (CR_of_Q R (1 # 2) * CRpow (CR_of_Q R (1 # 2)) n).
      2: reflexivity.
      rewrite <- CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace (2 * (1 # 2))%Q with 1%Q.
      * apply CRmult_1_l.
      * reflexivity.
Qed.

Lemma GeoHalfBelowTwo : forall {R : ConstructiveReals} (n:nat),
    CRsum (CRpow (CR_of_Q R (1#2))) n < CR_of_Q R 2.
Proof.
  intros. rewrite <- (CRplus_0_r (CR_of_Q R 2)), GeoFiniteSum.
  apply CRplus_lt_compat_l. rewrite <- CRopp_0.
  apply CRopp_gt_lt_contravar.
  apply CRpow_gt_zero. apply CR_of_Q_lt. reflexivity.
Qed.

Lemma GeoHalfTwo : forall {R : ConstructiveReals},
    series_cv (fun n => CRpow (CR_of_Q R (1#2)) n) (CR_of_Q R 2).
Proof.
  intro R.
  apply (CR_cv_eq _ (fun n => CR_of_Q R 2 - CRpow (CR_of_Q R (1 # 2)) n)).
  - intro n. rewrite GeoFiniteSum. reflexivity.
  - assert (forall n:nat, INR n < CRpow (CR_of_Q R 2) n).
    { induction n.
      - unfold INR; simpl.
        apply CRzero_lt_one.
      - apply (CRlt_le_trans _ (CRpow (CR_of_Q R 2) n + 1)).
        + unfold INR.
          rewrite Nat2Z.inj_succ, <- Z.add_1_l.
          rewrite (CR_of_Q_morph R _ (1 + (Z.of_nat n #1))).
          2: symmetry; apply Qinv_plus_distr. rewrite CR_of_Q_plus.
          rewrite CRplus_comm.
          apply CRplus_lt_compat_r, IHn.
        + setoid_replace (CRpow (CR_of_Q R 2) (S n))
            with (CRpow (CR_of_Q R 2) n + CRpow (CR_of_Q R 2) n).
          * apply CRplus_le_compat.
            -- apply CRle_refl.
            -- apply CRpow_ge_one. apply CR_of_Q_le. discriminate.
          * rewrite <- CR_double. reflexivity. }
    intros n. exists (Pos.to_nat n). intros.
    setoid_replace (CR_of_Q R 2 - CRpow (CR_of_Q R (1 # 2)) i - CR_of_Q R 2)
      with (- CRpow (CR_of_Q R (1 # 2)) i).
    + rewrite CRabs_opp. rewrite CRabs_right.
      * assert (0 < CR_of_Q R 2).
        { apply CR_of_Q_lt. reflexivity. }
        rewrite (CRpow_proper _ (CRinv R (CR_of_Q R 2) (inr H1))).
        -- rewrite CRpow_inv. apply CRlt_asym.
           apply (CRmult_lt_reg_l (CRpow (CR_of_Q R 2) i)).
           ++ apply CRpow_gt_zero, H1.
           ++ rewrite CRinv_r.
              apply (CRmult_lt_reg_r (CR_of_Q R (Z.pos n#1))).
              ** apply CR_of_Q_lt. reflexivity.
              ** rewrite CRmult_1_l, CRmult_assoc.
                 rewrite <- CR_of_Q_mult.
                 rewrite (CR_of_Q_morph R ((1 # n) * (Z.pos n # 1)) 1). 2: reflexivity.
                 rewrite CRmult_1_r. apply (CRle_lt_trans _ (INR i)).
                 2: apply H. apply CR_of_Q_le.
                 unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r. destruct i.
                 { exfalso. inversion H0. pose proof (Pos2Nat.is_pos n).
                   rewrite H3 in H2. inversion H2. }
                 apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
                 apply (Nat.le_trans _ _ _ H0). rewrite SuccNat2Pos.id_succ. apply Nat.le_refl.
        -- apply (CRmult_eq_reg_l (CR_of_Q R 2)).
           ++ right. exact H1.
           ++ rewrite CRinv_r. rewrite <- CR_of_Q_mult.
              setoid_replace (2 * (1 # 2))%Q with 1%Q.
              ** reflexivity.
              ** reflexivity.
      * apply CRlt_asym, CRpow_gt_zero.
        apply CR_of_Q_lt. reflexivity.
    + unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.
