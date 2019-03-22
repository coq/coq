(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(* The multiplication and division of Cauchy reals. *)

Require Import QArith.
Require Import Qabs.
Require Import Qround.
Require Import Logic.ConstructiveEpsilon.
Require Export Reals.ConstructiveCauchyReals.
Require CMorphisms.

Local Open Scope CReal_scope.

Fixpoint BoundFromZero (qn : nat -> Q) (k : nat) (A : positive) { struct k }
  : (forall n:nat, le k n -> Qlt (Qabs (qn n)) (Z.pos A # 1))
    -> { B : positive | forall n:nat, Qlt (Qabs (qn n)) (Z.pos B # 1) }.
Proof.
  intro H. destruct k.
  - exists A. intros. apply H. apply le_0_n.
  - destruct (Qarchimedean (Qabs (qn k))) as [a maj].
    apply (BoundFromZero qn k (Pos.max A a)).
    intros n H0. destruct (Nat.le_gt_cases n k).
    + pose proof (Nat.le_antisymm n k H1 H0). subst k.
      apply (Qlt_le_trans _ (Z.pos a # 1)). apply maj.
      unfold Qle; simpl. rewrite Pos.mul_1_r. rewrite Pos.mul_1_r.
      apply Pos.le_max_r.
    + apply (Qlt_le_trans _ (Z.pos A # 1)). apply H.
      apply H1. unfold Qle; simpl. rewrite Pos.mul_1_r. rewrite Pos.mul_1_r.
      apply Pos.le_max_l.
Qed.

Lemma QCauchySeq_bounded (qn : nat -> Q) (cvmod : positive -> nat)
  : QCauchySeq qn cvmod
    -> { A : positive | forall n:nat, Qlt (Qabs (qn n)) (Z.pos A # 1) }.
Proof.
  intros. remember (Zplus (Qnum (Qabs (qn (cvmod xH)))) 1) as z.
  assert (Z.lt 0 z) as zPos.
  { subst z. assert (Qle 0 (Qabs (qn (cvmod 1%positive)))).
    apply Qabs_nonneg. destruct (Qabs (qn (cvmod 1%positive))). simpl.
    unfold Qle in H0. simpl in H0. rewrite Zmult_1_r in H0.
    apply (Z.lt_le_trans 0 1). unfold Z.lt. auto.
    rewrite <- (Zplus_0_l 1). rewrite Zplus_assoc. apply Zplus_le_compat_r.
    rewrite Zplus_0_r. assumption. }
  assert { A : positive | forall n:nat,
          le (cvmod xH) n -> Qlt ((Qabs (qn n)) * (1#A)) 1 }.
  destruct z eqn:des.
  - exfalso. apply (Z.lt_irrefl 0). assumption.
  - exists p. intros. specialize (H xH (cvmod xH) n (le_refl _) H0).
    assert (Qlt (Qabs (qn n)) (Qabs (qn (cvmod 1%positive)) + 1)).
    { apply (Qplus_lt_l _ _ (-Qabs (qn (cvmod 1%positive)))).
      rewrite <- (Qplus_comm 1). rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
      rewrite Qplus_0_r. apply (Qle_lt_trans _ (Qabs (qn n - qn (cvmod 1%positive)))).
      apply Qabs_triangle_reverse. rewrite Qabs_Qminus. assumption. }
    apply (Qlt_le_trans _ ((Qabs (qn (cvmod 1%positive)) + 1) * (1#p))).
    apply Qmult_lt_r. unfold Qlt. simpl. unfold Z.lt. auto. assumption.
    unfold Qle. simpl. rewrite Zmult_1_r. rewrite Zmult_1_r. rewrite Zmult_1_r.
    rewrite Pos.mul_1_r. rewrite Pos2Z.inj_mul. rewrite Heqz.
    destruct (Qabs (qn (cvmod 1%positive))) eqn:desAbs.
    rewrite Z.mul_add_distr_l. rewrite Zmult_1_r.
    apply Zplus_le_compat_r. rewrite <- (Zmult_1_l (QArith_base.Qnum (Qnum # Qden))).
    rewrite Zmult_assoc. apply Zmult_le_compat_r. rewrite Zmult_1_r.
    simpl. unfold Z.le. rewrite <- Pos2Z.inj_compare.
    unfold Pos.compare. destruct Qden; discriminate.
    simpl. assert (Qle 0 (Qnum # Qden)). rewrite <- desAbs.
    apply Qabs_nonneg. unfold Qle in H2. simpl in H2. rewrite Zmult_1_r in H2.
    assumption.
  - exfalso. inversion zPos.
  - destruct H0. apply (BoundFromZero _ (cvmod xH) x). intros n H0.
    specialize (q n H0). setoid_replace (Z.pos x # 1)%Q with (/(1#x))%Q.
    rewrite <- (Qmult_1_l (/(1#x))). apply Qlt_shift_div_l.
    reflexivity. apply q. reflexivity.
Qed.

Lemma CReal_mult_cauchy
  : forall (xn yn zn : nat -> Q) (Ay Az : positive) (cvmod : positive -> nat),
    QSeqEquiv xn yn cvmod
    -> QCauchySeq zn Pos.to_nat
    -> (forall n:nat, Qlt (Qabs (yn n)) (Z.pos Ay # 1))
    -> (forall n:nat, Qlt (Qabs (zn n)) (Z.pos Az # 1))
    -> QSeqEquiv (fun n:nat => xn n * zn n) (fun n:nat => yn n * zn n)
                (fun p => max (cvmod (2 * (Pos.max Ay Az) * p)%positive)
                           (Pos.to_nat (2 * (Pos.max Ay Az) * p)%positive)).
Proof.
  intros xn yn zn Ay Az cvmod limx limz majy majz.
  remember (Pos.mul 2 (Pos.max Ay Az)) as z.
  intros k p q H H0.
  assert (Pos.to_nat k <> O) as kPos.
  { intro absurd. pose proof (Pos2Nat.is_pos k).
    rewrite absurd in H1. inversion H1. }
  setoid_replace (xn p * zn p - yn q * zn q)%Q
    with ((xn p - yn q) * zn p + yn q * (zn p - zn q))%Q.
  2: ring.
  apply (Qle_lt_trans _ (Qabs ((xn p - yn q) * zn p)
                         + Qabs (yn q * (zn p - zn q)))).
  apply Qabs_triangle. rewrite Qabs_Qmult. rewrite Qabs_Qmult.
  setoid_replace (1#k)%Q with ((1#2*k) + (1#2*k))%Q.
  apply Qplus_lt_le_compat.
  - apply (Qle_lt_trans _ ((1#z * k) * Qabs (zn p)%nat)).
    + apply Qmult_le_compat_r. apply Qle_lteq. left. apply limx.
      apply (le_trans _ (Init.Nat.max (cvmod (z * k)%positive) (Pos.to_nat (z * k)))).
      apply Nat.le_max_l. assumption.
      apply (le_trans _ (Init.Nat.max (cvmod (z * k)%positive) (Pos.to_nat (z * k)))).
      apply Nat.le_max_l. assumption. apply Qabs_nonneg.
    + subst z. rewrite <- (Qmult_1_r (1 # 2 * k)).
      rewrite <- Pos.mul_assoc. rewrite <- (Pos.mul_comm k). rewrite Pos.mul_assoc.
      rewrite (factorDenom _ _ (2 * k)). rewrite <- Qmult_assoc.
      apply Qmult_lt_l. unfold Qlt. simpl. unfold Z.lt. auto.
      apply (Qle_lt_trans _ (Qabs (zn p)%nat * (1 # Az))).
      rewrite <- (Qmult_comm (1 # Az)). apply Qmult_le_compat_r.
      unfold Qle. simpl. rewrite Pos2Z.inj_max. apply Z.le_max_r.
      apply Qabs_nonneg. rewrite <- (Qmult_inv_r (1#Az)).
      rewrite Qmult_comm. apply Qmult_lt_l. reflexivity.
      setoid_replace (/(1#Az))%Q with (Z.pos Az # 1)%Q. apply majz.
      reflexivity. intro abs. inversion abs.
  - apply (Qle_trans _ ((1 # z * k) * Qabs (yn q)%nat)).
    + rewrite Qmult_comm. apply Qmult_le_compat_r. apply Qle_lteq.
      left. apply limz.
      apply (le_trans _ (max (cvmod (z * k)%positive)
                             (Pos.to_nat (z * k)%positive))).
      apply Nat.le_max_r. assumption.
      apply (le_trans _ (max (cvmod (z * k)%positive)
                             (Pos.to_nat (z * k)%positive))).
      apply Nat.le_max_r. assumption. apply Qabs_nonneg.
    + subst z. rewrite <- (Qmult_1_r (1 # 2 * k)).
      rewrite <- Pos.mul_assoc. rewrite <- (Pos.mul_comm k). rewrite Pos.mul_assoc.
      rewrite (factorDenom _ _ (2 * k)). rewrite <- Qmult_assoc.
      apply Qle_lteq. left.
      apply Qmult_lt_l. unfold Qlt. simpl. unfold Z.lt. auto.
      apply (Qle_lt_trans _ (Qabs (yn q)%nat * (1 # Ay))).
      rewrite <- (Qmult_comm (1 # Ay)). apply Qmult_le_compat_r.
      unfold Qle. simpl. rewrite Pos2Z.inj_max. apply Z.le_max_l.
      apply Qabs_nonneg. rewrite <- (Qmult_inv_r (1#Ay)).
      rewrite Qmult_comm. apply Qmult_lt_l. reflexivity.
      setoid_replace (/(1#Ay))%Q with (Z.pos Ay # 1)%Q. apply majy.
      reflexivity. intro abs. inversion abs.
  - rewrite Qinv_plus_distr. unfold Qeq. reflexivity.
Qed.

Lemma linear_max : forall (p Ax Ay : positive) (i : nat),
  le (Pos.to_nat p) i
  -> (Init.Nat.max (Pos.to_nat (2 * Pos.max Ax Ay * p))
                 (Pos.to_nat (2 * Pos.max Ax Ay * p)) <= Pos.to_nat (2 * Pos.max Ax Ay) * i)%nat.
Proof.
  intros. rewrite max_l. 2: apply le_refl.
  rewrite Pos2Nat.inj_mul. apply Nat.mul_le_mono_nonneg.
  apply le_0_n. apply le_refl. apply le_0_n. apply H.
Qed.

Definition CReal_mult (x y : CReal) : CReal.
Proof.
  destruct x as [xn limx]. destruct y as [yn limy].
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
  pose proof (CReal_mult_cauchy xn xn yn Ax Ay Pos.to_nat limx limy majx majy).
  exists (fun n : nat => xn (Pos.to_nat (2 * Pos.max Ax Ay)* n)%nat
               * yn (Pos.to_nat (2 * Pos.max Ax Ay) * n)%nat).
  intros p n k H0 H1.
  apply H; apply linear_max; assumption.
Defined.

Infix "*" := CReal_mult : CReal_scope.

Lemma CReal_mult_unfold : forall x y : CReal,
    QSeqEquivEx (proj1_sig (CReal_mult x y))
                (fun n : nat => proj1_sig x n * proj1_sig y n)%Q.
Proof.
  intros [xn limx] [yn limy]. unfold CReal_mult ; simpl.
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
  simpl.
  pose proof (CReal_mult_cauchy xn xn yn Ax Ay Pos.to_nat limx limy majx majy).
  exists (fun p : positive =>
         Init.Nat.max (Pos.to_nat (2 * Pos.max Ax Ay * p))
           (Pos.to_nat (2 * Pos.max Ax Ay * p))).
  intros p n k H0 H1. rewrite max_l in H0, H1.
  2: apply le_refl. 2: apply le_refl.
  apply H. apply linear_max.
  apply (le_trans _ (Pos.to_nat (2 * Pos.max Ax Ay * p))).
  rewrite <- (mult_1_l (Pos.to_nat p)). rewrite Pos2Nat.inj_mul.
  apply Nat.mul_le_mono_nonneg. auto. apply Pos2Nat.is_pos.
  apply le_0_n. apply le_refl. apply H0. rewrite max_l.
  apply H1. apply le_refl.
Qed.

Lemma CReal_mult_assoc_bounded_r : forall (xn yn zn : nat -> Q),
    QSeqEquivEx xn yn (* both are Cauchy with same limit *)
    -> QSeqEquiv zn zn Pos.to_nat
    -> QSeqEquivEx (fun n => xn n * zn n)%Q (fun n => yn n * zn n)%Q.
Proof.
  intros. destruct H as [cvmod cveq].
  destruct (QCauchySeq_bounded yn (fun k => cvmod (2 * k)%positive)
                               (QSeqEquiv_cau_r xn yn cvmod cveq))
    as [Ay majy].
  destruct (QCauchySeq_bounded zn Pos.to_nat H0) as [Az majz].
  exists (fun p => max (cvmod (2 * (Pos.max Ay Az) * p)%positive)
               (Pos.to_nat (2 * (Pos.max Ay Az) * p)%positive)).
  apply CReal_mult_cauchy; assumption.
Qed.

Lemma CReal_mult_assoc : forall x y z : CReal,
    CRealEq (CReal_mult (CReal_mult x y) z)
            (CReal_mult x (CReal_mult y z)).
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig y n * proj1_sig z n)%Q).
  - apply (QSeqEquivEx_trans _ (fun n => proj1_sig (CReal_mult x y) n * proj1_sig z n)%Q).
    apply CReal_mult_unfold.
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; unfold CReal_mult; simpl.
    destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
    destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
    destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
    apply CReal_mult_assoc_bounded_r. 2: apply limz.
    simpl.
    pose proof (CReal_mult_cauchy xn xn yn Ax Ay Pos.to_nat limx limy majx majy).
    exists (fun p : positive =>
         Init.Nat.max (Pos.to_nat (2 * Pos.max Ax Ay * p))
                      (Pos.to_nat (2 * Pos.max Ax Ay * p))).
    intros p n k H0 H1. rewrite max_l in H0, H1.
    2: apply le_refl. 2: apply le_refl.
    apply H. apply linear_max.
    apply (le_trans _ (Pos.to_nat (2 * Pos.max Ax Ay * p))).
    rewrite <- (mult_1_l (Pos.to_nat p)). rewrite Pos2Nat.inj_mul.
    apply Nat.mul_le_mono_nonneg. auto. apply Pos2Nat.is_pos.
    apply le_0_n. apply le_refl. apply H0. rewrite max_l.
    apply H1. apply le_refl.
  - apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig (CReal_mult y z) n)%Q).
    2: apply QSeqEquivEx_sym; apply CReal_mult_unfold.
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; unfold CReal_mult; simpl.
    destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
    destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
    destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
    simpl.
    pose proof (CReal_mult_assoc_bounded_r (fun n0 : nat => yn n0 * zn n0)%Q (fun n : nat =>
          yn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat
          * zn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat)%Q xn)
      as [cvmod cveq].

    pose proof (CReal_mult_cauchy yn yn zn Ay Az Pos.to_nat limy limz majy majz).
    exists (fun p : positive =>
         Init.Nat.max (Pos.to_nat (2 * Pos.max Ay Az * p))
                      (Pos.to_nat (2 * Pos.max Ay Az * p))).
    intros p n k H0 H1. rewrite max_l in H0, H1.
    2: apply le_refl. 2: apply le_refl.
    apply H. rewrite max_l. apply H0. apply le_refl.
    apply linear_max.
    apply (le_trans _ (Pos.to_nat (2 * Pos.max Ay Az * p))).
    rewrite <- (mult_1_l (Pos.to_nat p)). rewrite Pos2Nat.inj_mul.
    apply Nat.mul_le_mono_nonneg. auto. apply Pos2Nat.is_pos.
    apply le_0_n. apply le_refl. apply H1.
    apply limx.
    exists cvmod. intros p k n H1 H2. specialize (cveq p k n H1 H2).
    setoid_replace (xn k * yn k * zn k -
     xn n *
     (yn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat *
      zn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat))%Q
      with ((fun n : nat => yn n * zn n * xn n) k -
            (fun n : nat =>
             yn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat *
             zn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat *
             xn n) n)%Q.
    apply cveq. ring.
Qed.

Lemma CReal_mult_comm : forall x y : CReal,
    CRealEq (CReal_mult x y) (CReal_mult y x).
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig y n * proj1_sig x n)%Q).
  destruct x as [xn limx], y as [yn limy]; simpl.
  2: apply QSeqEquivEx_sym; apply CReal_mult_unfold.
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy]; simpl.
  apply QSeqEquivEx_sym.

  pose proof (CReal_mult_cauchy yn yn xn Ay Ax Pos.to_nat limy limx majy majx).
  exists (fun p : positive =>
       Init.Nat.max (Pos.to_nat (2 * Pos.max Ay Ax * p))
                    (Pos.to_nat (2 * Pos.max Ay Ax * p))).
  intros p n k H0 H1. rewrite max_l in H0, H1.
  2: apply le_refl. 2: apply le_refl.
  rewrite (Qmult_comm (xn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat)).
  apply (H p n). rewrite max_l. apply H0. apply le_refl.
  rewrite max_l. apply (le_trans _ k). apply H1.
  rewrite <- (mult_1_l k). rewrite mult_assoc.
  apply Nat.mul_le_mono_nonneg. auto. rewrite mult_1_r.
  apply Pos2Nat.is_pos. apply le_0_n. apply le_refl.
  apply le_refl.
Qed.

Lemma CReal_mult_proper_l : forall x y z : CReal,
    CRealEq y z -> CRealEq (CReal_mult x y) (CReal_mult x z).
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig y n)%Q).
  apply CReal_mult_unfold.
  rewrite CRealEq_diff in H. rewrite <- CRealEq_modindep in H.
  apply QSeqEquivEx_sym.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig z n)%Q).
  apply CReal_mult_unfold.
  destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl.
  destruct H. simpl in H.
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
  pose proof (CReal_mult_cauchy yn zn xn Az Ax x H limx majz majx).
  apply QSeqEquivEx_sym.
  exists (fun p : positive =>
       Init.Nat.max (x (2 * Pos.max Az Ax * p)%positive)
                    (Pos.to_nat (2 * Pos.max Az Ax * p))).
  intros p n k H1 H2. specialize (H0 p n k H1 H2).
  setoid_replace (xn n * yn n - xn k * zn k)%Q
    with (yn n * xn n - zn k * xn k)%Q.
  apply H0. ring.
Qed.

Lemma CReal_mult_lt_0_compat : forall x y : CReal,
    CRealLt (inject_Q 0) x
    -> CRealLt (inject_Q 0) y
    -> CRealLt (inject_Q 0) (CReal_mult x y).
Proof.
  intros. destruct H as [x0 H], H0 as [x1 H0].
  pose proof (CRealLt_aboveSig (inject_Q 0) x x0 H).
  pose proof (CRealLt_aboveSig (inject_Q 0) y x1 H0).
  destruct x as [xn limx], y as [yn limy].
  simpl in H, H1, H2. simpl.
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
  destruct (Qarchimedean (/ (xn (Pos.to_nat x0) - 0 - (2 # x0)))).
  destruct (Qarchimedean (/ (yn (Pos.to_nat x1) - 0 - (2 # x1)))).
  exists (Pos.max x0 x~0 * Pos.max x1 x2~0)%positive.
  simpl. unfold Qminus. rewrite Qplus_0_r.
  rewrite <- Pos2Nat.inj_mul.
  unfold Qminus in H1, H2.
  specialize (H1 ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive).
  assert (Pos.max x1 x2~0 <= (Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive.
  { apply Pos2Nat.inj_le.
    rewrite Pos.mul_assoc. rewrite Pos2Nat.inj_mul.
    rewrite <- (mult_1_l (Pos.to_nat (Pos.max x1 x2~0))).
    rewrite mult_assoc. apply Nat.mul_le_mono_nonneg. auto.
    rewrite mult_1_r. apply Pos2Nat.is_pos. apply le_0_n.
    apply le_refl. }
  specialize (H2 ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive H3).
  rewrite Qplus_0_r in H1, H2.
  apply (Qlt_trans _ ((2 # Pos.max x0 x~0) * (2 # Pos.max x1 x2~0))).
  unfold Qlt; simpl. assert (forall p : positive, (Z.pos p < Z.pos p~0)%Z).
  intro p. rewrite <- (Z.mul_1_l (Z.pos p)).
  replace (Z.pos p~0) with (2 * Z.pos p)%Z. apply Z.mul_lt_mono_pos_r.
  apply Pos2Z.is_pos. reflexivity. reflexivity.
  apply H4.
  apply (Qlt_trans _ ((2 # Pos.max x0 x~0) * (yn (Pos.to_nat ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0)))))).
  apply Qmult_lt_l. reflexivity. apply H2. apply Qmult_lt_r.
  apply (Qlt_trans 0 (2 # Pos.max x1 x2~0)). reflexivity. apply H2.
  apply H1. rewrite Pos.mul_comm. apply Pos2Nat.inj_le.
  rewrite <- Pos.mul_assoc. rewrite Pos2Nat.inj_mul.
  rewrite <- (mult_1_r (Pos.to_nat (Pos.max x0 x~0))).
  rewrite <- mult_assoc. apply Nat.mul_le_mono_nonneg.
  apply le_0_n. apply le_refl. auto.
  rewrite mult_1_l. apply Pos2Nat.is_pos.
Qed.

Lemma CReal_mult_plus_distr_l : forall r1 r2 r3 : CReal,
    r1 * (r2 + r3) == (r1 * r2) + (r1 * r3).
Proof.
  intros x y z. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n
                                    * (proj1_sig (CReal_plus y z) n))%Q).
  apply CReal_mult_unfold.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig (CReal_mult x y) n
                                    + proj1_sig (CReal_mult x z) n))%Q.
  2: apply QSeqEquivEx_sym; exists (fun p => Pos.to_nat (2 * p))
  ; apply CReal_plus_unfold.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n
                                    * (proj1_sig y n + proj1_sig z n))%Q).
  - pose proof (CReal_plus_unfold y z).
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl; simpl in H.
    destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
    destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
    destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
    pose proof (CReal_mult_cauchy (fun n => yn (n + (n + 0))%nat + zn (n + (n + 0))%nat)%Q
                                  (fun n => yn n + zn n)%Q
                                  xn (Ay + Az) Ax
                                  (fun p => Pos.to_nat (2 * p)) H limx).
    exists (fun p : positive => (Pos.to_nat (2 * (2 * Pos.max (Ay + Az) Ax * p)))).
    intros p n k H1 H2.
    setoid_replace (xn n * (yn (n + (n + 0))%nat + zn (n + (n + 0))%nat) - xn k * (yn k + zn k))%Q
      with ((yn (n + (n + 0))%nat + zn (n + (n + 0))%nat) * xn n - (yn k + zn k) * xn k)%Q.
    2: ring.
    assert (Pos.to_nat (2 * Pos.max (Ay + Az) Ax * p) <=
            Pos.to_nat 2 * Pos.to_nat (2 * Pos.max (Ay + Az) Ax * p))%nat.
    { rewrite (Pos2Nat.inj_mul 2).
      rewrite <- (mult_1_l (Pos.to_nat (2 * Pos.max (Ay + Az) Ax * p))).
      rewrite mult_assoc. apply Nat.mul_le_mono_nonneg. auto.
      simpl. auto. apply le_0_n. apply le_refl. }
    apply H0. intro n0. apply (Qle_lt_trans _ (Qabs (yn n0) + Qabs (zn n0))).
    apply Qabs_triangle. rewrite Pos2Z.inj_add.
    rewrite <- Qinv_plus_distr. apply Qplus_lt_le_compat.
    apply majy. apply Qlt_le_weak. apply majz.
    apply majx. rewrite max_l.
    apply H1. rewrite (Pos2Nat.inj_mul 2). apply H3.
    rewrite max_l. apply H2. rewrite (Pos2Nat.inj_mul 2).
    apply H3.
  - destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl.
    destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
    destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
    destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
    simpl.
    exists (fun p : positive => (Pos.to_nat (2 * (Pos.max (Pos.max Ax Ay) Az) * (2 * p)))).
    intros p n k H H0.
    setoid_replace (xn n * (yn n + zn n) -
     (xn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat *
      yn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat +
      xn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat *
      zn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat))%Q
      with (xn n * yn n - (xn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat *
                           yn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat)
            + (xn n * zn n - xn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat *
                             zn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat))%Q.
    2: ring.
    apply (Qle_lt_trans _ (Qabs (xn n * yn n - (xn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat *
                                                yn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat))
                           + Qabs (xn n * zn n - xn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat *
                             zn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat))).
    apply Qabs_triangle.
    setoid_replace (1#p)%Q with ((1#2*p) + (1#2*p))%Q.
    apply Qplus_lt_le_compat.
    + pose proof (CReal_mult_cauchy xn xn yn Ax Ay Pos.to_nat limx limy).
      apply H1. apply majx. apply majy. rewrite max_l.
      apply (le_trans _ (Pos.to_nat (2 * Pos.max (Pos.max Ax Ay) Az * (2 * p)))).
      rewrite (Pos.mul_comm 2). rewrite <- Pos.mul_assoc.
      rewrite <- (Pos.mul_comm (Pos.max (Pos.max Ax Ay) Az)).
      rewrite <- Pos.mul_assoc.
      rewrite Pos2Nat.inj_mul.
      rewrite (Pos2Nat.inj_mul (Pos.max (Pos.max Ax Ay) Az)).
      apply Nat.mul_le_mono_nonneg. apply le_0_n.
      apply Pos2Nat.inj_le. apply Pos.le_max_l.
      apply le_0_n. apply le_refl. apply H. apply le_refl.
      rewrite max_l. apply (le_trans _ k).
      apply (le_trans _ (Pos.to_nat (2 * Pos.max (Pos.max Ax Ay) Az * (2 * p)))).
      rewrite (Pos.mul_comm 2). rewrite <- Pos.mul_assoc.
      rewrite <- (Pos.mul_comm (Pos.max (Pos.max Ax Ay) Az)).
      rewrite <- Pos.mul_assoc.
      rewrite Pos2Nat.inj_mul.
      rewrite (Pos2Nat.inj_mul (Pos.max (Pos.max Ax Ay) Az)).
      apply Nat.mul_le_mono_nonneg. apply le_0_n.
      apply Pos2Nat.inj_le. apply Pos.le_max_l.
      apply le_0_n. apply le_refl. apply H0.
      rewrite <- (mult_1_l k). rewrite mult_assoc.
      apply Nat.mul_le_mono_nonneg. auto.
      rewrite mult_1_r. apply Pos2Nat.is_pos. apply le_0_n.
      apply le_refl. apply le_refl.
    + apply Qlt_le_weak.
      pose proof (CReal_mult_cauchy xn xn zn Ax Az Pos.to_nat limx limz).
      apply H1. apply majx. apply majz. rewrite max_l. 2: apply le_refl.
      apply (le_trans _ (Pos.to_nat (2 * Pos.max (Pos.max Ax Ay) Az * (2 * p)))).
      rewrite (Pos.mul_comm 2). rewrite <- Pos.mul_assoc.
      rewrite <- (Pos.mul_comm (Pos.max (Pos.max Ax Ay) Az)).
      rewrite <- Pos.mul_assoc.
      rewrite Pos2Nat.inj_mul.
      rewrite (Pos2Nat.inj_mul (Pos.max (Pos.max Ax Ay) Az)).
      apply Nat.mul_le_mono_nonneg. apply le_0_n.
      rewrite <- Pos.max_assoc. rewrite (Pos.max_comm Ay Az).
      rewrite Pos.max_assoc. apply Pos2Nat.inj_le. apply Pos.le_max_l.
      apply le_0_n. apply le_refl. apply H.
      rewrite max_l. apply (le_trans _ k).
      apply (le_trans _ (Pos.to_nat (2 * Pos.max (Pos.max Ax Ay) Az * (2 * p)))).
      rewrite (Pos.mul_comm 2). rewrite <- Pos.mul_assoc.
      rewrite <- (Pos.mul_comm (Pos.max (Pos.max Ax Ay) Az)).
      rewrite <- Pos.mul_assoc.
      rewrite Pos2Nat.inj_mul.
      rewrite (Pos2Nat.inj_mul (Pos.max (Pos.max Ax Ay) Az)).
      apply Nat.mul_le_mono_nonneg. apply le_0_n.
      rewrite <- Pos.max_assoc. rewrite (Pos.max_comm Ay Az).
      rewrite Pos.max_assoc. apply Pos2Nat.inj_le. apply Pos.le_max_l.
      apply le_0_n. apply le_refl. apply H0.
      rewrite <- (mult_1_l k). rewrite mult_assoc.
      apply Nat.mul_le_mono_nonneg. auto.
      rewrite mult_1_r. apply Pos2Nat.is_pos. apply le_0_n.
      apply le_refl. apply le_refl.
    + rewrite Qinv_plus_distr. unfold Qeq. reflexivity.
Qed.

Lemma CReal_mult_plus_distr_r : forall r1 r2 r3 : CReal,
    (r2 + r3) * r1 == (r2 * r1) + (r3 * r1).
Proof.
  intros.
  rewrite CReal_mult_comm, CReal_mult_plus_distr_l,
  <- (CReal_mult_comm r1), <- (CReal_mult_comm r1).
  reflexivity.
Qed.

Lemma CReal_mult_1_l : forall r: CReal, 1 * r == r.
Proof.
  intros [rn limr]. split.
  - intros [m maj]. simpl in maj.
    destruct (QCauchySeq_bounded (fun _ : nat => 1%Q) Pos.to_nat (ConstCauchy 1)).
    destruct (QCauchySeq_bounded rn Pos.to_nat limr).
    simpl in maj. rewrite Qmult_1_l in maj.
    specialize (limr m).
    apply (Qlt_not_le (2 # m) (1 # m)).
    apply (Qlt_trans _ (rn (Pos.to_nat m) - rn (Pos.to_nat (Pos.max x x0)~0 * Pos.to_nat m)%nat)).
    apply maj.
    apply (Qle_lt_trans _ (Qabs (rn (Pos.to_nat m) - rn (Pos.to_nat (Pos.max x x0)~0 * Pos.to_nat m)%nat))).
    apply Qle_Qabs. apply limr. apply le_refl.
    rewrite <- (mult_1_l (Pos.to_nat m)). rewrite mult_assoc.
    apply Nat.mul_le_mono_nonneg. auto. rewrite mult_1_r.
    apply Pos2Nat.is_pos. apply le_0_n. apply le_refl.
    apply Z.mul_le_mono_nonneg. discriminate. discriminate.
    discriminate. apply Z.le_refl.
  - intros [m maj]. simpl in maj.
    destruct (QCauchySeq_bounded (fun _ : nat => 1%Q) Pos.to_nat (ConstCauchy 1)).
    destruct (QCauchySeq_bounded rn Pos.to_nat limr).
    simpl in maj. rewrite Qmult_1_l in maj.
    specialize (limr m).
    apply (Qlt_not_le (2 # m) (1 # m)).
    apply (Qlt_trans _ (rn (Pos.to_nat (Pos.max x x0)~0 * Pos.to_nat m)%nat - rn (Pos.to_nat m))).
    apply maj.
    apply (Qle_lt_trans _ (Qabs (rn (Pos.to_nat (Pos.max x x0)~0 * Pos.to_nat m)%nat - rn (Pos.to_nat m)))).
    apply Qle_Qabs. apply limr.
    rewrite <- (mult_1_l (Pos.to_nat m)). rewrite mult_assoc.
    apply Nat.mul_le_mono_nonneg. auto. rewrite mult_1_r.
    apply Pos2Nat.is_pos. apply le_0_n. apply le_refl.
    apply le_refl. apply Z.mul_le_mono_nonneg. discriminate. discriminate.
    discriminate. apply Z.le_refl.
Qed.

Lemma CReal_isRingExt : ring_eq_ext CReal_plus CReal_mult CReal_opp CRealEq.
Proof.
  split.
  - intros x y H z t H0. apply CReal_plus_morph; assumption.
  - intros x y H z t H0. apply (CRealEq_trans _ (CReal_mult x t)).
    apply CReal_mult_proper_l. apply H0.
    apply (CRealEq_trans _ (CReal_mult t x)). apply CReal_mult_comm.
    apply (CRealEq_trans _ (CReal_mult t y)).
    apply CReal_mult_proper_l. apply H.  apply CReal_mult_comm.
  - intros x y H. apply (CReal_plus_eq_reg_l x).
    apply (CRealEq_trans _ (inject_Q 0)). apply CReal_plus_opp_r.
    apply (CRealEq_trans _ (CReal_plus y (CReal_opp y))).
    apply CRealEq_sym. apply CReal_plus_opp_r.
    apply CReal_plus_proper_r. apply CRealEq_sym. apply H.
Qed.

Lemma CReal_isRing : ring_theory (inject_Q 0) (inject_Q 1)
                                 CReal_plus CReal_mult
                                 CReal_minus CReal_opp
                                 CRealEq.
Proof.
  intros. split.
  - apply CReal_plus_0_l.
  - apply CReal_plus_comm.
  - intros x y z. symmetry. apply CReal_plus_assoc.
  - apply CReal_mult_1_l.
  - apply CReal_mult_comm.
  - intros x y z. symmetry. apply CReal_mult_assoc.
  - intros x y z. rewrite <- (CReal_mult_comm z).
    rewrite CReal_mult_plus_distr_l.
    apply (CRealEq_trans _ (CReal_plus (CReal_mult x z) (CReal_mult z y))).
    apply CReal_plus_proper_r. apply CReal_mult_comm.
    apply CReal_plus_proper_l. apply CReal_mult_comm.
  - intros x y. apply CRealEq_refl.
  - apply CReal_plus_opp_r.
Qed.

Add Parametric Morphism : CReal_mult
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_mult_morph.
Proof.
  apply CReal_isRingExt.
Qed.

Instance CReal_mult_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRealEq)) CReal_mult.
Proof.
  apply CReal_isRingExt.
Qed.

Add Parametric Morphism : CReal_opp
    with signature CRealEq ==> CRealEq
      as CReal_opp_morph.
Proof.
  apply (Ropp_ext CReal_isRingExt).
Qed.

Instance CReal_opp_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq CRealEq) CReal_opp.
Proof.
  apply CReal_isRingExt.
Qed.

Add Parametric Morphism : CReal_minus
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_minus_morph.
Proof.
  intros. unfold CReal_minus. rewrite H,H0. reflexivity.
Qed.

Instance CReal_minus_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRealEq)) CReal_minus.
Proof.
  intros x y exy z t ezt. unfold CReal_minus. rewrite exy,ezt. reflexivity.
Qed.

Add Ring CRealRing : CReal_isRing.

(**********)
Lemma CReal_mult_0_l : forall r, 0 * r == 0.
Proof.
  intro; ring.
Qed.

Lemma CReal_mult_0_r : forall r, r * 0 == 0.
Proof.
  intro; ring.
Qed.

(**********)
Lemma CReal_mult_1_r : forall r, r * 1 == r.
Proof.
  intro; ring.
Qed.

Lemma CReal_opp_mult_distr_l
  : forall r1 r2 : CReal, - (r1 * r2) == (- r1) * r2.
Proof.
  intros. ring.
Qed.

Lemma CReal_opp_mult_distr_r
  : forall r1 r2 : CReal, - (r1 * r2) == r1 * (- r2).
Proof.
  intros. ring.
Qed.

Lemma CReal_mult_lt_compat_l : forall x y z : CReal,
    0 < x -> y < z -> x*y < x*z.
Proof.
  intros. apply (CReal_plus_lt_reg_l
                   (CReal_opp (CReal_mult x y))).
  rewrite CReal_plus_comm. pose proof CReal_plus_opp_r.
  unfold CReal_minus in H1. rewrite H1.
  rewrite CReal_mult_comm, CReal_opp_mult_distr_l, CReal_mult_comm.
  rewrite <- CReal_mult_plus_distr_l.
  apply CReal_mult_lt_0_compat. exact H.
  apply (CReal_plus_lt_reg_l y).
  rewrite CReal_plus_comm, CReal_plus_0_l.
  rewrite <- CReal_plus_assoc, H1, CReal_plus_0_l. exact H0.
Qed.

Lemma CReal_mult_lt_compat_r : forall x y z : CReal,
    0 < x -> y < z -> y*x < z*x.
Proof.
  intros. rewrite <- (CReal_mult_comm x), <- (CReal_mult_comm x).
  apply (CReal_mult_lt_compat_l x); assumption.
Qed.

Lemma CReal_mult_eq_reg_l : forall (r r1 r2 : CReal),
    r # 0
    -> CRealEq (CReal_mult r r1) (CReal_mult r r2)
    -> CRealEq r1 r2.
Proof.
  intros. destruct H; split.
  - intro abs. apply (CReal_mult_lt_compat_l (-r)) in abs.
    rewrite <- CReal_opp_mult_distr_l, <- CReal_opp_mult_distr_l, H0 in abs.
    exact (CRealLt_irrefl _ abs). apply (CReal_plus_lt_reg_l r).
    rewrite CReal_plus_opp_r, CReal_plus_comm, CReal_plus_0_l. exact c.
  - intro abs. apply (CReal_mult_lt_compat_l (-r)) in abs.
    rewrite <- CReal_opp_mult_distr_l, <- CReal_opp_mult_distr_l, H0 in abs.
    exact (CRealLt_irrefl _ abs). apply (CReal_plus_lt_reg_l r).
    rewrite CReal_plus_opp_r, CReal_plus_comm, CReal_plus_0_l. exact c.
  - intro abs. apply (CReal_mult_lt_compat_l r) in abs. rewrite H0 in abs.
    exact (CRealLt_irrefl _ abs). exact c.
  - intro abs. apply (CReal_mult_lt_compat_l r) in abs. rewrite H0 in abs.
    exact (CRealLt_irrefl _ abs). exact c.
Qed.

Lemma CReal_abs_appart_zero : forall (x : CReal) (n : positive),
    Qlt (2#n) (Qabs (proj1_sig x (Pos.to_nat n)))
    -> 0 # x.
Proof.
  intros. destruct x as [xn xcau]. simpl in H.
  destruct (Qlt_le_dec 0 (xn (Pos.to_nat n))).
  - left. exists n; simpl. rewrite Qabs_pos in H.
    ring_simplify. exact H. apply Qlt_le_weak. exact q.
  - right. exists n; simpl. rewrite Qabs_neg in H.
    unfold Qminus. rewrite Qplus_0_l. exact H. exact q.
Qed.


(*********************************************************)
(** * Field                                              *)
(*********************************************************)

Lemma CRealArchimedean
  : forall x:CReal, { n:Z  &  x < inject_Q (n#1) < x+2 }.
Proof.
  (* Locate x within 1/4 and pick the first integer above this interval. *)
  intros [xn limx].
  pose proof (Qlt_floor (xn 4%nat + (1#4))). unfold inject_Z in H.
  pose proof (Qfloor_le (xn 4%nat + (1#4))). unfold inject_Z in H0.
  remember (Qfloor (xn 4%nat + (1#4)))%Z as n.
  exists (n+1)%Z. split.
  - assert (Qlt 0 ((n + 1 # 1) - (xn 4%nat + (1 # 4)))) as epsPos.
    { unfold Qminus. rewrite <- Qlt_minus_iff. exact H. }
    destruct (Qarchimedean (/((1#2)*((n + 1 # 1) - (xn 4%nat + (1 # 4)))))) as [k kmaj].
    exists (Pos.max 4 k). simpl.
    apply (Qlt_trans _ ((n + 1 # 1) - (xn 4%nat + (1 # 4)))).
    + setoid_replace (Z.pos k # 1)%Q with (/(1#k))%Q in kmaj. 2: reflexivity.
      rewrite <- Qinv_lt_contravar in kmaj. 2: reflexivity.
      apply (Qle_lt_trans _ (2#k)).
      rewrite <- (Qmult_le_l _ _ (1#2)).
      setoid_replace ((1 # 2) * (2 # k))%Q with (1#k)%Q. 2: reflexivity.
      setoid_replace ((1 # 2) * (2 # Pos.max 4 k))%Q with (1#Pos.max 4 k)%Q. 2: reflexivity.
      unfold Qle; simpl. apply Pos2Z.pos_le_pos. apply Pos.le_max_r.
      reflexivity.
      rewrite <- (Qmult_lt_l _ _ (1#2)).
      setoid_replace ((1 # 2) * (2 # k))%Q with (1#k)%Q. exact kmaj.
      reflexivity. reflexivity. rewrite <- (Qmult_0_r (1#2)).
      rewrite Qmult_lt_l. exact epsPos. reflexivity.
    + rewrite <- (Qplus_lt_r _ _ (xn (Pos.to_nat (Pos.max 4 k)) - (n + 1 # 1) + (1#4))).
      ring_simplify.
      apply (Qle_lt_trans _ (Qabs (xn (Pos.to_nat (Pos.max 4 k)) - xn 4%nat))).
      apply Qle_Qabs. apply limx.
      rewrite Pos2Nat.inj_max. apply Nat.le_max_l. apply le_refl.
  - apply (CReal_plus_lt_reg_l (-(2))). ring_simplify.
    exists 4%positive. simpl.
    rewrite <- Qinv_plus_distr.
    rewrite <- (Qplus_lt_r _ _ ((n#1) - (1#2))). ring_simplify.
    apply (Qle_lt_trans _ (xn 4%nat + (1 # 4)) _ H0).
    unfold Pos.to_nat; simpl.
    rewrite <- (Qplus_lt_r _ _ (-xn 4%nat)). ring_simplify.
    reflexivity.
Defined.

Definition Rup_pos (x : CReal)
  : { n : positive  &  x < inject_Q (Z.pos n # 1) }.
Proof.
  intros. destruct (CRealArchimedean x) as [p [maj _]].
  destruct p.
  - exists 1%positive. apply (CReal_lt_trans _ 0 _ maj). apply CRealLt_0_1.
  - exists p. exact maj.
  - exists 1%positive. apply (CReal_lt_trans _ (inject_Q (Z.neg p # 1)) _ maj).
    apply (CReal_lt_trans _ 0). apply inject_Q_lt. reflexivity.
    apply CRealLt_0_1.
Qed.

Lemma CRealLtDisjunctEpsilon : forall a b c d : CReal,
    (CRealLtProp a b \/ CRealLtProp c d) -> CRealLt a b  +  CRealLt c d.
Proof.
  intros.
  assert (exists n : nat, n <> O /\
             (Qlt (2 # Pos.of_nat n) (proj1_sig b n - proj1_sig a n)
              \/ Qlt (2 # Pos.of_nat n) (proj1_sig d n - proj1_sig c n))).
  { destruct H. destruct H as [n maj]. exists (Pos.to_nat n). split.
    intro abs. destruct (Pos2Nat.is_succ n). rewrite H in abs.
    inversion abs. left. rewrite Pos2Nat.id. apply maj.
    destruct H as [n maj]. exists (Pos.to_nat n). split.
    intro abs. destruct (Pos2Nat.is_succ n). rewrite H in abs.
    inversion abs. right. rewrite Pos2Nat.id. apply maj. }
  apply constructive_indefinite_ground_description_nat in H0.
  - destruct H0 as [n [nPos maj]].
    destruct (Qlt_le_dec (2 # Pos.of_nat n)
                         (proj1_sig b n - proj1_sig a n)).
    left. exists (Pos.of_nat n). rewrite Nat2Pos.id. apply q. apply nPos.
    assert (2 # Pos.of_nat n < proj1_sig d n - proj1_sig c n)%Q.
    destruct maj. exfalso.
    apply (Qlt_not_le (2 # Pos.of_nat n) (proj1_sig b n - proj1_sig a n)); assumption.
    assumption. clear maj. right. exists (Pos.of_nat n). rewrite Nat2Pos.id.
    apply H0. apply nPos.
  - clear H0. clear H. intro n. destruct n. right.
    intros [abs _]. exact (abs (eq_refl O)).
    destruct (Qlt_le_dec (2 # Pos.of_nat (S n)) (proj1_sig b (S n) - proj1_sig a (S n))).
    left. split. discriminate. left. apply q.
    destruct (Qlt_le_dec (2 # Pos.of_nat (S n)) (proj1_sig d (S n) - proj1_sig c (S n))).
    left. split. discriminate. right. apply q0.
    right. intros [_ [abs|abs]].
    apply (Qlt_not_le (2 # Pos.of_nat (S n))
                      (proj1_sig b (S n) - proj1_sig a (S n))); assumption.
    apply (Qlt_not_le (2 # Pos.of_nat (S n))
                      (proj1_sig d (S n) - proj1_sig c (S n))); assumption.
Qed.

Lemma CRealShiftReal : forall (x : CReal) (k : nat),
    QCauchySeq (fun n => proj1_sig x (plus n k)) Pos.to_nat.
Proof.
  intros x k n p q H H0.
  destruct x as [xn cau]; unfold proj1_sig.
  destruct k. rewrite plus_0_r. rewrite plus_0_r. apply cau; assumption.
  specialize (cau (n + Pos.of_nat (S k))%positive (p + S k)%nat (q + S k)%nat).
  apply (Qlt_trans _ (1 # n + Pos.of_nat (S k))).
  apply cau. rewrite Pos2Nat.inj_add. rewrite Nat2Pos.id.
  apply Nat.add_le_mono_r. apply H. discriminate.
  rewrite Pos2Nat.inj_add. rewrite Nat2Pos.id.
  apply Nat.add_le_mono_r. apply H0. discriminate.
  apply Pos2Nat.inj_lt; simpl. rewrite Pos2Nat.inj_add.
  rewrite <- (plus_0_r (Pos.to_nat n)). rewrite <- plus_assoc.
  apply Nat.add_lt_mono_l. apply Pos2Nat.is_pos.
Qed.

Lemma CRealShiftEqual : forall (x : CReal) (k : nat),
    CRealEq x (exist _ (fun n => proj1_sig x (plus n k)) (CRealShiftReal x k)).
Proof.
  intros. split.
  - intros [n maj]. destruct x as [xn cau]; simpl in maj.
    specialize (cau n (Pos.to_nat n + k)%nat (Pos.to_nat n)).
    apply Qlt_not_le in maj. apply maj. clear maj.
    apply (Qle_trans _ (Qabs (xn (Pos.to_nat n + k)%nat - xn (Pos.to_nat n)))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Zlt_le_weak.
    apply cau. rewrite <- (plus_0_r (Pos.to_nat n)).
    rewrite <- plus_assoc. apply Nat.add_le_mono_l. apply le_0_n.
    apply le_refl. apply Z.mul_le_mono_pos_r. apply Pos2Z.is_pos.
    discriminate.
  - intros [n maj]. destruct x as [xn cau]; simpl in maj.
    specialize (cau n (Pos.to_nat n) (Pos.to_nat n + k)%nat).
    apply Qlt_not_le in maj. apply maj. clear maj.
    apply (Qle_trans _ (Qabs (xn (Pos.to_nat n) - xn (Pos.to_nat n + k)%nat))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Zlt_le_weak.
    apply cau. apply le_refl. rewrite <- (plus_0_r (Pos.to_nat n)).
    rewrite <- plus_assoc. apply Nat.add_le_mono_l. apply le_0_n.
    apply Z.mul_le_mono_pos_r. apply Pos2Z.is_pos. discriminate.
Qed.

(* Find an equal negative real number, which rational sequence
   stays below 0, so that it can be inversed. *)
Definition CRealNegShift (x : CReal)
  : CRealLt x (inject_Q 0)
    -> { y : prod positive CReal | CRealEq x (snd y)
                                   /\ forall n:nat, Qlt (proj1_sig (snd y) n) (-1 # fst y) }.
Proof.
  intro xNeg.
  pose proof (CRealLt_aboveSig x (inject_Q 0)).
  pose proof (CRealShiftReal x).
  pose proof (CRealShiftEqual x).
  destruct xNeg as [n maj], x as [xn cau]; simpl in maj.
  specialize (H n maj); simpl in H.
  destruct (Qarchimedean (/ (0 - xn (Pos.to_nat n) - (2 # n)))) as [a _].
  remember (Pos.max n a~0) as k.
  clear Heqk. clear maj. clear n.
  exists (pair k
          (exist _ (fun n => xn (plus n (Pos.to_nat k))) (H0 (Pos.to_nat k)))).
  split. apply H1. intro n. simpl. apply Qlt_minus_iff.
  destruct n.
  - specialize (H k).
    unfold Qminus in H. rewrite Qplus_0_l in H. apply Qlt_minus_iff in H.
    unfold Qminus. rewrite Qplus_comm.
    apply (Qlt_trans _ (- xn (Pos.to_nat k)%nat - (2 #k))). apply H.
    unfold Qminus. simpl. apply Qplus_lt_r.
    apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
    reflexivity. apply Pos.le_refl.
  - apply (Qlt_trans _ (-(2 # k) - xn (S n + Pos.to_nat k)%nat)).
    rewrite <- (Nat2Pos.id (S n)). rewrite <- Pos2Nat.inj_add.
    specialize (H (Pos.of_nat (S n) + k)%positive).
    unfold Qminus in H. rewrite Qplus_0_l in H. apply Qlt_minus_iff in H.
    unfold Qminus. rewrite Qplus_comm. apply H. apply Pos2Nat.inj_le.
    rewrite <- (plus_0_l (Pos.to_nat k)). rewrite Pos2Nat.inj_add.
    apply Nat.add_le_mono_r. apply le_0_n. discriminate.
    apply Qplus_lt_l.
    apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
    reflexivity.
Qed.

Definition CRealPosShift (x : CReal)
  : inject_Q 0 < x
    -> { y : prod positive CReal | CRealEq x (snd y)
                                   /\ forall n:nat, Qlt (1 # fst y) (proj1_sig (snd y) n) }.
Proof.
  intro xPos.
  pose proof (CRealLt_aboveSig (inject_Q 0) x).
  pose proof (CRealShiftReal x).
  pose proof (CRealShiftEqual x).
  destruct xPos as [n maj], x as [xn cau]; simpl in maj.
  simpl in H. specialize (H n).
  destruct (Qarchimedean (/ (xn (Pos.to_nat n) - 0 - (2 # n)))) as [a _].
  specialize (H maj); simpl in H.
  remember (Pos.max n a~0) as k.
  clear Heqk. clear maj. clear n.
  exists (pair k
               (exist _ (fun n => xn (plus n (Pos.to_nat k))) (H0 (Pos.to_nat k)))).
  split. apply H1. intro n. simpl. apply Qlt_minus_iff.
  destruct n.
  - specialize (H k).
    unfold Qminus in H. rewrite Qplus_0_r in H.
    simpl. rewrite <- Qlt_minus_iff.
    apply (Qlt_trans _ (2 #k)).
    apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
    reflexivity. apply H. apply Pos.le_refl.
  - rewrite <- Qlt_minus_iff. apply (Qlt_trans _ (2 # k)).
    apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
    reflexivity. specialize (H (Pos.of_nat (S n) + k)%positive).
    unfold Qminus in H. rewrite Qplus_0_r in H.
    rewrite Pos2Nat.inj_add in H. rewrite Nat2Pos.id in H.
    apply H. apply Pos2Nat.inj_le.
    rewrite <- (plus_0_l (Pos.to_nat k)). rewrite Pos2Nat.inj_add.
    apply Nat.add_le_mono_r. apply le_0_n. discriminate.
Qed.

Lemma CReal_inv_neg : forall (yn : nat -> Q) (k : positive),
    (QCauchySeq yn Pos.to_nat)
    -> (forall n : nat, yn n < -1 # k)%Q
    -> QCauchySeq (fun n : nat => / yn (Pos.to_nat k ^ 2 * n)%nat) Pos.to_nat.
Proof.
  (* Prove the inverse sequence is Cauchy *)
  intros yn k cau maj n p q H0 H1.
  setoid_replace (/ yn (Pos.to_nat k ^ 2 * p)%nat -
                  / yn (Pos.to_nat k ^ 2 * q)%nat)%Q
    with ((yn (Pos.to_nat k ^ 2 * q)%nat -
           yn (Pos.to_nat k ^ 2 * p)%nat)
            / (yn (Pos.to_nat k ^ 2 * q)%nat *
               yn (Pos.to_nat k ^ 2 * p)%nat)).
  + apply (Qle_lt_trans _ (Qabs (yn (Pos.to_nat k ^ 2 * q)%nat
                                 - yn (Pos.to_nat k ^ 2 * p)%nat)
                                / (1 # (k^2)))).
    assert (1 # k ^ 2
            < Qabs (yn (Pos.to_nat k ^ 2 * q)%nat * yn (Pos.to_nat k ^ 2 * p)%nat))%Q.
    { rewrite Qabs_Qmult. unfold "^"%positive; simpl.
      rewrite factorDenom. rewrite Pos.mul_1_r.
      apply (Qlt_trans _ ((1#k) * Qabs (yn (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat))).
      apply Qmult_lt_l. reflexivity. rewrite Qabs_neg.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat).
      apply Qlt_minus_iff in maj. apply Qlt_minus_iff.
      rewrite Qplus_comm. setoid_replace (-(1#k))%Q with (-1 # k)%Q. apply maj.
      reflexivity. apply (Qle_trans _ (-1 # k)). apply Zlt_le_weak.
      apply maj. discriminate.
      apply Qmult_lt_r. apply (Qlt_trans 0 (1#k)). reflexivity.
      rewrite Qabs_neg.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat).
      apply Qlt_minus_iff in maj. apply Qlt_minus_iff.
      rewrite Qplus_comm. setoid_replace (-(1#k))%Q with (-1 # k)%Q. apply maj.
      reflexivity. apply (Qle_trans _ (-1 # k)). apply Zlt_le_weak.
      apply maj. discriminate.
      rewrite Qabs_neg.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * q)%nat).
      apply Qlt_minus_iff in maj. apply Qlt_minus_iff.
      rewrite Qplus_comm. setoid_replace (-(1#k))%Q with (-1 # k)%Q. apply maj.
      reflexivity. apply (Qle_trans _ (-1 # k)). apply Zlt_le_weak.
      apply maj. discriminate. }
    unfold Qdiv. rewrite Qabs_Qmult. rewrite Qabs_Qinv.
    rewrite Qmult_comm. rewrite <- (Qmult_comm (/ (1 # k ^ 2))).
    apply Qmult_le_compat_r. apply Qlt_le_weak.
    rewrite <- Qmult_1_l. apply Qlt_shift_div_r.
    apply (Qlt_trans 0 (1 # k ^ 2)). reflexivity. apply H.
    rewrite Qmult_comm. apply Qlt_shift_div_l.
    reflexivity. rewrite Qmult_1_l. apply H.
    apply Qabs_nonneg. simpl in maj.
    specialize (cau (n * (k^2))%positive
                    (Pos.to_nat k ^ 2 * q)%nat
                    (Pos.to_nat k ^ 2 * p)%nat).
    apply Qlt_shift_div_r. reflexivity.
    apply (Qlt_le_trans _ (1 # n * k ^ 2)). apply cau.
    rewrite Pos2Nat.inj_mul. rewrite mult_comm.
    unfold "^"%positive. simpl. rewrite Pos2Nat.inj_mul.
    rewrite <- mult_assoc. rewrite <- mult_assoc.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    rewrite (mult_1_r). rewrite Pos.mul_1_r.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply (le_trans _ (q+0)). rewrite plus_0_r. assumption.
    rewrite plus_0_r. apply le_refl.
    rewrite Pos2Nat.inj_mul. rewrite mult_comm.
    unfold "^"%positive; simpl. rewrite Pos2Nat.inj_mul.
    rewrite <- mult_assoc. rewrite <- mult_assoc.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    rewrite (mult_1_r). rewrite Pos.mul_1_r.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply (le_trans _ (p+0)). rewrite plus_0_r. assumption.
    rewrite plus_0_r. apply le_refl.
    rewrite factorDenom. apply Qle_refl.
  + field. split. intro abs.
    specialize (maj (Pos.to_nat k ^ 2 * p)%nat).
    rewrite abs in maj. inversion maj.
    intro abs.
    specialize (maj (Pos.to_nat k ^ 2 * q)%nat).
    rewrite abs in maj. inversion maj.
Qed.

Lemma CReal_inv_pos : forall (yn : nat -> Q) (k : positive),
    (QCauchySeq yn Pos.to_nat)
    -> (forall n : nat, 1 # k < yn n)%Q
    -> QCauchySeq (fun n : nat => / yn (Pos.to_nat k ^ 2 * n)%nat) Pos.to_nat.
Proof.
  intros yn k cau maj n p q H0 H1.
  setoid_replace (/ yn (Pos.to_nat k ^ 2 * p)%nat -
                  / yn (Pos.to_nat k ^ 2 * q)%nat)%Q
    with ((yn (Pos.to_nat k ^ 2 * q)%nat -
           yn (Pos.to_nat k ^ 2 * p)%nat)
            / (yn (Pos.to_nat k ^ 2 * q)%nat *
               yn (Pos.to_nat k ^ 2 * p)%nat)).
  + apply (Qle_lt_trans _ (Qabs (yn (Pos.to_nat k ^ 2 * q)%nat
                                 - yn (Pos.to_nat k ^ 2 * p)%nat)
                                / (1 # (k^2)))).
    assert (1 # k ^ 2
            < Qabs (yn (Pos.to_nat k ^ 2 * q)%nat * yn (Pos.to_nat k ^ 2 * p)%nat))%Q.
    { rewrite Qabs_Qmult. unfold "^"%positive; simpl.
      rewrite factorDenom. rewrite Pos.mul_1_r.
      apply (Qlt_trans _ ((1#k) * Qabs (yn (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat))).
      apply Qmult_lt_l. reflexivity. rewrite Qabs_pos.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat).
      apply maj. apply (Qle_trans _ (1 # k)).
      discriminate. apply Zlt_le_weak. apply maj.
      apply Qmult_lt_r. apply (Qlt_trans 0 (1#k)). reflexivity.
      rewrite Qabs_pos.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat).
      apply maj. apply (Qle_trans _ (1 # k)). discriminate.
      apply Zlt_le_weak. apply maj.
      rewrite Qabs_pos.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * q)%nat).
      apply maj. apply (Qle_trans _ (1 # k)). discriminate.
      apply Zlt_le_weak. apply maj. }
    unfold Qdiv. rewrite Qabs_Qmult. rewrite Qabs_Qinv.
    rewrite Qmult_comm. rewrite <- (Qmult_comm (/ (1 # k ^ 2))).
    apply Qmult_le_compat_r. apply Qlt_le_weak.
    rewrite <- Qmult_1_l. apply Qlt_shift_div_r.
    apply (Qlt_trans 0 (1 # k ^ 2)). reflexivity. apply H.
    rewrite Qmult_comm. apply Qlt_shift_div_l.
    reflexivity. rewrite Qmult_1_l. apply H.
    apply Qabs_nonneg. simpl in maj.
    specialize (cau (n * (k^2))%positive
                    (Pos.to_nat k ^ 2 * q)%nat
                    (Pos.to_nat k ^ 2 * p)%nat).
    apply Qlt_shift_div_r. reflexivity.
    apply (Qlt_le_trans _ (1 # n * k ^ 2)). apply cau.
    rewrite Pos2Nat.inj_mul. rewrite mult_comm.
    unfold "^"%positive. simpl. rewrite Pos2Nat.inj_mul.
    rewrite <- mult_assoc. rewrite <- mult_assoc.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    rewrite (mult_1_r). rewrite Pos.mul_1_r.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply (le_trans _ (q+0)). rewrite plus_0_r. assumption.
    rewrite plus_0_r. apply le_refl.
    rewrite Pos2Nat.inj_mul. rewrite mult_comm.
    unfold "^"%positive; simpl. rewrite Pos2Nat.inj_mul.
    rewrite <- mult_assoc. rewrite <- mult_assoc.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    rewrite (mult_1_r). rewrite Pos.mul_1_r.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply (le_trans _ (p+0)). rewrite plus_0_r. assumption.
    rewrite plus_0_r. apply le_refl.
    rewrite factorDenom. apply Qle_refl.
  + field. split. intro abs.
    specialize (maj (Pos.to_nat k ^ 2 * p)%nat).
    rewrite abs in maj. inversion maj.
    intro abs.
    specialize (maj (Pos.to_nat k ^ 2 * q)%nat).
    rewrite abs in maj. inversion maj.
Qed.

Definition CReal_inv (x : CReal) (xnz : x # 0) : CReal.
Proof.
  destruct xnz as [xNeg | xPos].
  - destruct (CRealNegShift x xNeg) as [[k y] [_ maj]].
    destruct y as [yn cau]; unfold proj1_sig, snd, fst in maj.
    exists (fun n => Qinv (yn (mult (Pos.to_nat k^2) n))).
    apply (CReal_inv_neg yn). apply cau. apply maj.
  - destruct (CRealPosShift x xPos) as [[k y] [_ maj]].
    destruct y as [yn cau]; unfold proj1_sig, snd, fst in maj.
    exists (fun n => Qinv (yn (mult (Pos.to_nat k^2) n))).
    apply (CReal_inv_pos yn). apply cau. apply maj.
Defined.

Notation "/ x" := (CReal_inv x) (at level 35, right associativity) : CReal_scope.

Lemma CReal_inv_0_lt_compat
  : forall (r : CReal) (rnz : r # 0),
    0 < r -> 0 < ((/ r) rnz).
Proof.
  intros. unfold CReal_inv. simpl.
  destruct rnz.
  - exfalso. apply CRealLt_asym in H. contradiction.
  - destruct (CRealPosShift r c) as [[k rpos] [req maj]].
    clear req. destruct rpos as [rn cau]; simpl in maj.
    unfold CRealLt; simpl.
    destruct (Qarchimedean (rn 1%nat)) as [A majA].
    exists (2 * (A + 1))%positive. unfold Qminus. rewrite Qplus_0_r.
    rewrite <- (Qmult_1_l (Qinv (rn (Pos.to_nat k * (Pos.to_nat k * 1) * Pos.to_nat (2 * (A + 1)))%nat))).
    apply Qlt_shift_div_l. apply (Qlt_trans 0 (1#k)). reflexivity.
    apply maj. rewrite <- (Qmult_inv_r (Z.pos A + 1 # 1)).
    setoid_replace (2 # 2 * (A + 1))%Q with (Qinv (Z.pos A + 1 # 1)).
    2: reflexivity.
    rewrite Qmult_comm. apply Qmult_lt_r. reflexivity.
    rewrite mult_1_r. rewrite <- Pos2Nat.inj_mul. rewrite <- Pos2Nat.inj_mul.
    rewrite <- (Qplus_lt_l _ _ (- rn 1%nat)).
    apply (Qle_lt_trans _ (Qabs (rn (Pos.to_nat (k * k * (2 * (A + 1)))) + - rn 1%nat))).
    apply Qle_Qabs. apply (Qlt_le_trans _ 1). apply cau.
    apply Pos2Nat.is_pos. apply le_refl.
    rewrite <- Qinv_plus_distr. rewrite <- (Qplus_comm 1).
    rewrite <- Qplus_0_r. rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
    rewrite Qplus_le_r. rewrite Qplus_0_l. apply Qlt_le_weak.
    apply Qlt_minus_iff in majA. apply majA.
    intro abs. inversion abs.
Qed.

Lemma CReal_linear_shift : forall (x : CReal) (k : nat),
    le 1 k -> QCauchySeq (fun n => proj1_sig x (k * n)%nat) Pos.to_nat.
Proof.
  intros [xn limx] k lek p n m H H0. unfold proj1_sig.
  apply limx. apply (le_trans _ n). apply H.
  rewrite <- (mult_1_l n). rewrite mult_assoc.
  apply Nat.mul_le_mono_nonneg_r. apply le_0_n.
  rewrite mult_1_r. apply lek. apply (le_trans _ m). apply H0.
  rewrite <- (mult_1_l m). rewrite mult_assoc.
  apply Nat.mul_le_mono_nonneg_r. apply le_0_n.
  rewrite mult_1_r. apply lek.
Qed.

Lemma CReal_linear_shift_eq : forall (x : CReal) (k : nat) (kPos : le 1 k),
    CRealEq x
    (exist (fun n : nat -> Q => QCauchySeq n Pos.to_nat)
           (fun n : nat => proj1_sig x (k * n)%nat) (CReal_linear_shift x k kPos)).
Proof.
  intros. apply CRealEq_diff. intro n.
  destruct x as [xn limx]; unfold proj1_sig.
  specialize (limx n (Pos.to_nat n) (k * Pos.to_nat n)%nat).
  apply (Qle_trans _ (1 # n)). apply Qlt_le_weak. apply limx.
  apply le_refl. rewrite <- (mult_1_l (Pos.to_nat n)).
  rewrite mult_assoc. apply Nat.mul_le_mono_nonneg_r. apply le_0_n.
  rewrite mult_1_r. apply kPos. apply Z.mul_le_mono_nonneg_r.
  discriminate. discriminate.
Qed.

Lemma CReal_inv_l : forall (r:CReal) (rnz : r # 0),
        ((/ r) rnz) * r == 1.
Proof.
  intros. unfold CReal_inv; simpl.
  destruct rnz.
  - (* r < 0 *) destruct (CRealNegShift r c) as [[k rneg] [req maj]].
    simpl in req. apply CRealEq_diff. apply CRealEq_modindep.
    apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : nat, proj1_sig s n < -1 # k) -> CReal) := rneg in
            fun maj0 : forall n : nat, yn n < -1 # k =>
            exist (fun x : nat -> Q => QCauchySeq x Pos.to_nat)
              (fun n : nat => Qinv (yn (Pos.to_nat k * (Pos.to_nat k * 1) * n))%nat)
              (CReal_inv_neg yn k cau maj0)) maj) rneg)))%Q.
    + apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply req.
    + assert (le 1 (Pos.to_nat k * (Pos.to_nat k * 1))%nat). rewrite mult_1_r.
      rewrite <- Pos2Nat.inj_mul. apply Pos2Nat.is_pos.
      apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : nat, proj1_sig s n < -1 # k) -> CReal) := rneg in
            fun maj0 : forall n : nat, yn n < -1 # k =>
            exist (fun x : nat -> Q => QCauchySeq x Pos.to_nat)
              (fun n : nat => Qinv (yn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
              (CReal_inv_neg yn k cau maj0)) maj)
                                    (exist _ (fun n => proj1_sig rneg (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat) (CReal_linear_shift rneg _ H)))))%Q.
      apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply CReal_linear_shift_eq.
      destruct r as [rn limr], rneg as [rnn limneg]; simpl.
      destruct (QCauchySeq_bounded
                  (fun n : nat => Qinv (rnn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
                  Pos.to_nat (CReal_inv_neg rnn k limneg maj)).
      destruct (QCauchySeq_bounded
            (fun n : nat => rnn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat)
            Pos.to_nat
            (CReal_linear_shift
               (exist (fun x0 : nat -> Q => QCauchySeq x0 Pos.to_nat) rnn limneg)
               (Pos.to_nat k * (Pos.to_nat k * 1)) H)) ; simpl.
      exists (fun n => 1%nat). intros p n m H0 H1. rewrite Qmult_comm.
      rewrite Qmult_inv_r. unfold Qminus. rewrite Qplus_opp_r.
      reflexivity. intro abs.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1)
                       * (Pos.to_nat (Pos.max x x0)~0 * n))%nat).
      simpl in maj. rewrite abs in maj. inversion maj.
  - (* r > 0 *) destruct (CRealPosShift r c) as [[k rneg] [req maj]].
    simpl in req. apply CRealEq_diff. apply CRealEq_modindep.
    apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : nat, 1 # k < proj1_sig s n) -> CReal) := rneg in
            fun maj0 : forall n : nat, 1 # k < yn n =>
            exist (fun x : nat -> Q => QCauchySeq x Pos.to_nat)
              (fun n : nat => Qinv (yn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
              (CReal_inv_pos yn k cau maj0)) maj) rneg)))%Q.
    + apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply req.
    + assert (le 1 (Pos.to_nat k * (Pos.to_nat k * 1))%nat). rewrite mult_1_r.
      rewrite <- Pos2Nat.inj_mul. apply Pos2Nat.is_pos.
      apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : nat, 1 # k < proj1_sig s n) -> CReal) := rneg in
            fun maj0 : forall n : nat, 1 # k < yn n =>
            exist (fun x : nat -> Q => QCauchySeq x Pos.to_nat)
              (fun n : nat => Qinv (yn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
              (CReal_inv_pos yn k cau maj0)) maj)
                                    (exist _ (fun n => proj1_sig rneg (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat) (CReal_linear_shift rneg _ H)))))%Q.
      apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply CReal_linear_shift_eq.
      destruct r as [rn limr], rneg as [rnn limneg]; simpl.
      destruct (QCauchySeq_bounded
                  (fun n : nat => Qinv (rnn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
                  Pos.to_nat (CReal_inv_pos rnn k limneg maj)).
      destruct (QCauchySeq_bounded
            (fun n : nat => rnn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat)
            Pos.to_nat
            (CReal_linear_shift
               (exist (fun x0 : nat -> Q => QCauchySeq x0 Pos.to_nat) rnn limneg)
               (Pos.to_nat k * (Pos.to_nat k * 1)) H)) ; simpl.
      exists (fun n => 1%nat). intros p n m H0 H1. rewrite Qmult_comm.
      rewrite Qmult_inv_r. unfold Qminus. rewrite Qplus_opp_r.
      reflexivity. intro abs.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1)
                       * (Pos.to_nat (Pos.max x x0)~0 * n))%nat).
      simpl in maj. rewrite abs in maj. inversion maj.
Qed.

Lemma CReal_inv_r : forall (r:CReal) (rnz : r # 0),
        r * ((/ r) rnz) == 1.
Proof.
  intros. rewrite CReal_mult_comm, CReal_inv_l.
  reflexivity.
Qed.

Lemma CReal_inv_1 : forall nz : 1 # 0, (/ 1) nz == 1.
Proof.
  intros. rewrite <- (CReal_mult_1_l ((/1) nz)). rewrite CReal_inv_r.
  reflexivity.
Qed.

Lemma CReal_inv_mult_distr :
  forall r1 r2 (r1nz : r1 # 0) (r2nz : r2 # 0) (rmnz : (r1*r2) # 0),
    (/ (r1 * r2)) rmnz == (/ r1) r1nz * (/ r2) r2nz.
Proof.
  intros. apply (CReal_mult_eq_reg_l r1). exact r1nz.
  rewrite <- CReal_mult_assoc. rewrite CReal_inv_r. rewrite CReal_mult_1_l.
  apply (CReal_mult_eq_reg_l r2). exact r2nz.
  rewrite CReal_inv_r. rewrite <- CReal_mult_assoc.
  rewrite (CReal_mult_comm r2 r1). rewrite CReal_inv_r.
  reflexivity.
Qed.

Lemma Rinv_eq_compat : forall x y (rxnz : x # 0) (rynz : y # 0),
    x == y
    -> (/ x) rxnz == (/ y) rynz.
Proof.
  intros. apply (CReal_mult_eq_reg_l x). exact rxnz.
 rewrite CReal_inv_r, H, CReal_inv_r. reflexivity.
Qed.

Lemma CReal_mult_lt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  intros z x y H H0.
  apply (CReal_mult_lt_compat_l ((/z) (inr H))) in H0.
  repeat rewrite <- CReal_mult_assoc in H0. rewrite CReal_inv_l in H0.
  repeat rewrite CReal_mult_1_l in H0. apply H0.
  apply CReal_inv_0_lt_compat. exact H.
Qed.

Lemma CReal_mult_lt_reg_r : forall r r1 r2, 0 < r -> r1 * r < r2 * r -> r1 < r2.
Proof.
  intros.
  apply CReal_mult_lt_reg_l with r.
  exact H.
  now rewrite 2!(CReal_mult_comm r).
Qed.

Lemma CReal_mult_eq_reg_r : forall r r1 r2, r1 * r == r2 * r -> r # 0 -> r1 == r2.
Proof.
  intros. apply (CReal_mult_eq_reg_l r). exact H0.
  now rewrite 2!(CReal_mult_comm r).
Qed.

Lemma CReal_mult_eq_compat_l : forall r r1 r2, r1 == r2 -> r * r1 == r * r2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma CReal_mult_eq_compat_r : forall r r1 r2, r1 == r2 -> r1 * r == r2 * r.
Proof.
  intros. rewrite H. reflexivity.
Qed.

(* In particular x * y == 1 implies that 0 # x, 0 # y and
   that x and y are inverses of each other. *)
Lemma CReal_mult_pos_appart_zero : forall x y : CReal, 0 < x * y -> 0 # x.
Proof.
  intros. destruct (linear_order_T 0 x 1 (CRealLt_0_1)).
  left. exact c. destruct (linear_order_T (CReal_opp 1) x 0).
  rewrite <- CReal_opp_0. apply CReal_opp_gt_lt_contravar, CRealLt_0_1.
  2: right; exact c0.
  pose proof (CRealLt_above _ _ H). destruct H0 as [k kmaj].
  simpl in kmaj.
  apply CRealLt_above in c. destruct c as [i imaj]. simpl in imaj.
  apply CRealLt_above in c0. destruct c0 as [j jmaj]. simpl in jmaj.
  pose proof (CReal_abs_appart_zero y).
  destruct x as [xn xcau], y as [yn ycau]. simpl in kmaj.
  destruct (QCauchySeq_bounded xn Pos.to_nat xcau) as [a amaj],
  (QCauchySeq_bounded yn Pos.to_nat ycau) as [b bmaj]; simpl in kmaj.
  clear amaj bmaj. simpl in imaj, jmaj. simpl in H0.
  specialize (kmaj (Pos.max k (Pos.max i j)) (Pos.le_max_l _ _)).
  destruct (H0 ((Pos.max a b)~0 * (Pos.max k (Pos.max i j)))%positive).
  - apply (Qlt_trans _ (2#k)).
    + unfold Qlt. rewrite <- Z.mul_lt_mono_pos_l. 2: reflexivity.
      unfold Qden. apply Pos2Z.pos_lt_pos.
      apply (Pos.le_lt_trans _ (1 * Pos.max k (Pos.max i j))).
      rewrite Pos.mul_1_l. apply Pos.le_max_l.
      apply Pos2Nat.inj_lt. do 2 rewrite Pos2Nat.inj_mul.
      rewrite <- Nat.mul_lt_mono_pos_r. 2: apply Pos2Nat.is_pos.
      fold (2*Pos.max a b)%positive. rewrite Pos2Nat.inj_mul.
      apply Nat.lt_1_mul_pos. auto. apply Pos2Nat.is_pos.
    + apply (Qlt_le_trans _ _ _ kmaj). unfold Qminus. rewrite Qplus_0_r.
      rewrite <- (Qmult_1_l (Qabs (yn (Pos.to_nat ((Pos.max a b)~0 * Pos.max k (Pos.max i j)))))).
      apply (Qle_trans _ _ _ (Qle_Qabs _)). rewrite Qabs_Qmult.
      replace (Pos.to_nat (Pos.max a b)~0 * Pos.to_nat (Pos.max k (Pos.max i j)))%nat
        with (Pos.to_nat ((Pos.max a b)~0 * Pos.max k (Pos.max i j))).
      2: apply Pos2Nat.inj_mul.
      apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
      apply Qabs_Qle_condition. split.
      apply Qlt_le_weak. apply Qlt_minus_iff, (Qlt_trans _ (2#j)).
      reflexivity. apply jmaj.
      apply (Pos.le_trans _ (1 * Pos.max k (Pos.max i j))).
      rewrite Pos.mul_1_l.
      apply (Pos.le_trans _ (Pos.max i j) _ (Pos.le_max_r _ _)).
      apply Pos.le_max_r.
      apply Pos2Nat.inj_le. do 2 rewrite Pos2Nat.inj_mul.
      rewrite <- Nat.mul_le_mono_pos_r. 2: apply Pos2Nat.is_pos.
      apply Pos2Nat.is_pos.
      apply Qlt_le_weak. apply Qlt_minus_iff, (Qlt_trans _ (2#i)).
      reflexivity. apply imaj.
      apply (Pos.le_trans _ (1 * Pos.max k (Pos.max i j))).
      rewrite Pos.mul_1_l.
      apply (Pos.le_trans _ (Pos.max i j) _ (Pos.le_max_l _ _)).
      apply Pos.le_max_r.
      apply Pos2Nat.inj_le. do 2 rewrite Pos2Nat.inj_mul.
      rewrite <- Nat.mul_le_mono_pos_r. 2: apply Pos2Nat.is_pos.
      apply Pos2Nat.is_pos.
  - left. apply (CReal_mult_lt_reg_r (exist _ yn ycau) _ _ c).
    rewrite CReal_mult_0_l. exact H.
  - right. apply (CReal_mult_lt_reg_r (CReal_opp (exist _ yn ycau))).
    rewrite <- CReal_opp_0. apply CReal_opp_gt_lt_contravar. exact c.
    rewrite CReal_mult_0_l, <- CReal_opp_0, <- CReal_opp_mult_distr_r.
    apply CReal_opp_gt_lt_contravar. exact H.
Qed.

Fixpoint pow (r:CReal) (n:nat) : CReal :=
  match n with
    | O => 1
    | S n => r * (pow r n)
  end.


Lemma CReal_mult_le_compat_l_half : forall r r1 r2,
    0 < r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros. intro abs. apply (CReal_mult_lt_reg_l) in abs.
  contradiction. apply H.
Qed.

Lemma CReal_invQ : forall (b : positive) (pos : Qlt 0 (Z.pos b # 1)),
    CRealEq (CReal_inv (inject_Q (Z.pos b # 1)) (inr (CReal_injectQPos (Z.pos b # 1) pos)))
            (inject_Q (1 # b)).
Proof.
  intros.
  apply (CReal_mult_eq_reg_l (inject_Q (Z.pos b # 1))).
  - right. apply CReal_injectQPos. exact pos.
  - rewrite CReal_mult_comm, CReal_inv_l.
    apply CRealEq_diff. intro n. simpl;
    destruct (QCauchySeq_bounded (fun _ : nat => 1 # b)%Q Pos.to_nat (ConstCauchy (1 # b))),
    (QCauchySeq_bounded (fun _ : nat => Z.pos b # 1)%Q Pos.to_nat (ConstCauchy (Z.pos b # 1))); simpl.
    do 2 rewrite Pos.mul_1_r. rewrite Z.pos_sub_diag. discriminate.
Qed.

Definition CRealQ_dense (a b : CReal)
  : a < b -> { q : Q  &  a < inject_Q q < b }.
Proof.
  (* Locate a and b at the index given by a<b,
     and pick the middle rational number. *)
  intros [p pmaj].
  exists ((proj1_sig a (Pos.to_nat p) + proj1_sig b (Pos.to_nat p)) * (1#2))%Q.
  split.
  - apply (CReal_le_lt_trans _ _ _ (inject_Q_compare a p)). apply inject_Q_lt.
    apply (Qmult_lt_l _ _ 2). reflexivity.
    apply (Qplus_lt_l _ _ (-2*proj1_sig a (Pos.to_nat p))).
    field_simplify. field_simplify in pmaj.
    setoid_replace (-2#2)%Q with (-1)%Q. 2: reflexivity.
    setoid_replace (2*(1#p))%Q with (2#p)%Q. 2: reflexivity.
    rewrite Qplus_comm. exact pmaj.
  - apply (CReal_plus_lt_reg_l (-b)).
    rewrite CReal_plus_opp_l.
    apply (CReal_plus_lt_reg_r
             (-inject_Q ((proj1_sig a (Pos.to_nat p) + proj1_sig b (Pos.to_nat p)) * (1 # 2)))).
    rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r, CReal_plus_0_l.
    rewrite <- opp_inject_Q.
    apply (CReal_le_lt_trans _ _ _ (inject_Q_compare (-b) p)). apply inject_Q_lt.
    apply (Qmult_lt_l _ _ 2). reflexivity.
    apply (Qplus_lt_l _ _ (2*proj1_sig b (Pos.to_nat p))).
    destruct b as [bn bcau]; simpl. simpl in pmaj.
    field_simplify. field_simplify in pmaj.
    setoid_replace (-2#2)%Q with (-1)%Q. 2: reflexivity.
    setoid_replace (2*(1#p))%Q with (2#p)%Q. 2: reflexivity. exact pmaj.
Qed.

Lemma inject_Q_mult : forall q r : Q,
    inject_Q (q * r) == inject_Q q * inject_Q r.
Proof.
  split.
  - intros [n maj]. simpl in maj.
    destruct (QCauchySeq_bounded (fun _ : nat => q) Pos.to_nat (ConstCauchy q)).
    destruct (QCauchySeq_bounded (fun _ : nat => r) Pos.to_nat (ConstCauchy r)).
    simpl in maj. ring_simplify in maj. discriminate maj.
  - intros [n maj]. simpl in maj.
    destruct (QCauchySeq_bounded (fun _ : nat => q) Pos.to_nat (ConstCauchy q)).
    destruct (QCauchySeq_bounded (fun _ : nat => r) Pos.to_nat (ConstCauchy r)).
    simpl in maj. ring_simplify in maj. discriminate maj.
Qed.
