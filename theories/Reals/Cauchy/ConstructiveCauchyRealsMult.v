(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
Require Export ConstructiveCauchyReals.
Require CMorphisms.

Local Open Scope CReal_scope.

Definition QCauchySeq_bound (qn : positive -> Q) (cvmod : positive -> positive)
  : positive
  := match Qnum (qn (cvmod 1%positive)) with
     | Z0 => 1%positive
     | Z.pos p => p + 1
     | Z.neg p => p + 1
     end.

Lemma QCauchySeq_bounded_prop (qn : positive -> Q) (cvmod : positive -> positive)
  : QCauchySeq qn cvmod
    -> forall n:positive, Pos.le (cvmod 1%positive) n
                    -> Qlt (Qabs (qn n)) (Z.pos (QCauchySeq_bound qn cvmod) # 1).
Proof.
  intros H n H0. unfold QCauchySeq_bound.
  specialize (H 1%positive (cvmod 1%positive) n (Pos.le_refl _) H0).
  destruct (qn (cvmod 1%positive)) as [a b]. unfold Qnum.
  rewrite Qabs_Qminus in H.
  apply (Qplus_lt_l _ _ (-Qabs (a#b))).
  apply (Qlt_le_trans _ 1).
  exact (Qle_lt_trans _ _ _ (Qabs_triangle_reverse (qn n) (a#b)) H).
  assert (forall p : positive,
             (1 <= (Z.pos (p + 1) # 1) + - (Z.pos p # b))%Q).
  { intro p. unfold Qle, Qopp, Qplus, Qnum, Qden.
    rewrite Z.mul_1_r, Z.mul_1_r, Pos2Z.inj_add, Pos.mul_1_l.
    apply (Z.add_le_mono_l _ _ (Z.pos p -Z.pos b)).
    ring_simplify. apply (Z.le_trans _ (Z.pos p * 1)).
    rewrite Z.mul_1_r. apply Z.le_refl.
    apply Z.mul_le_mono_nonneg_l. discriminate. destruct b; discriminate. }
  destruct a.
  - setoid_replace (Qabs (0#b)) with 0%Q. 2: reflexivity.
    rewrite Qplus_0_r. apply Qle_refl.
  - apply H1.
  - apply H1.
Qed.

Lemma CReal_mult_cauchy
  : forall (xn yn zn : positive -> Q) (Ay Az : positive) (cvmod : positive -> positive),
    QSeqEquiv xn yn cvmod
    -> QCauchySeq zn id
    -> (forall n:positive, Pos.le (cvmod 2%positive) n
              -> Qlt (Qabs (yn n)) (Z.pos Ay # 1))
    -> (forall n:positive, Pos.le 1 n
              -> Qlt (Qabs (zn n)) (Z.pos Az # 1))
    -> QSeqEquiv (fun n:positive => xn n * zn n) (fun n:positive => yn n * zn n)
                (fun p => Pos.max (Pos.max (cvmod 2%positive)
                                (cvmod (2 * (Pos.max Ay Az) * p)%positive))
                               (2 * (Pos.max Ay Az) * p)%positive).
Proof.
  intros xn yn zn Ay Az cvmod limx limz majy majz.
  remember (Pos.mul 2 (Pos.max Ay Az)) as z.
  intros k p q H H0.
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
      apply (Pos.le_trans _ (Pos.max (cvmod (z * k)%positive) (z * k))).
      apply Pos.le_max_l. refine (Pos.le_trans _ _ _ _ H).
      rewrite <- Pos.max_assoc. apply Pos.le_max_r.
      apply (Pos.le_trans _ (Pos.max (cvmod (z * k)%positive) (z * k))).
      apply Pos.le_max_l. refine (Pos.le_trans _ _ _ _ H0).
      rewrite <- Pos.max_assoc. apply Pos.le_max_r. apply Qabs_nonneg.
    + subst z. rewrite <- (Qmult_1_r (1 # 2 * k)).
      rewrite <- Pos.mul_assoc. rewrite <- (Pos.mul_comm k). rewrite Pos.mul_assoc.
      rewrite (factorDenom _ _ (2 * k)). rewrite <- Qmult_assoc.
      apply Qmult_lt_l. reflexivity.
      apply (Qle_lt_trans _ (Qabs (zn p)%nat * (1 # Az))).
      rewrite <- (Qmult_comm (1 # Az)). apply Qmult_le_compat_r.
      unfold Qle. simpl. rewrite Pos2Z.inj_max. apply Z.le_max_r.
      apply Qabs_nonneg. rewrite <- (Qmult_inv_r (1#Az)).
      2: intro abs; inversion abs.
      rewrite Qmult_comm. apply Qmult_lt_l. reflexivity.
      setoid_replace (/(1#Az))%Q with (Z.pos Az # 1)%Q.
      2: reflexivity.
      apply majz. refine (Pos.le_trans _ _ _ _ H).
      apply (Pos.le_trans _ (2 * Pos.max Ay Az * k)).
      discriminate. apply Pos.le_max_r.
  - apply (Qle_trans _ ((1 # z * k) * Qabs (yn q)%nat)).
    + rewrite Qmult_comm. apply Qmult_le_compat_r. apply Qle_lteq.
      left. apply limz.
      apply (Pos.le_trans _ (Pos.max (cvmod (z * k)%positive)
                             (z * k)%positive)).
      apply Pos.le_max_r. refine (Pos.le_trans _ _ _ _ H).
      rewrite <- Pos.max_assoc. apply Pos.le_max_r.
      apply (Pos.le_trans _ (Pos.max (cvmod (z * k)%positive)
                             (z * k)%positive)).
      apply Pos.le_max_r. refine (Pos.le_trans _ _ _ _ H0).
      rewrite <- Pos.max_assoc. apply Pos.le_max_r.
      apply Qabs_nonneg.
    + subst z. rewrite <- (Qmult_1_r (1 # 2 * k)).
      rewrite <- Pos.mul_assoc. rewrite <- (Pos.mul_comm k). rewrite Pos.mul_assoc.
      rewrite (factorDenom _ _ (2 * k)). rewrite <- Qmult_assoc.
      apply Qle_lteq. left.
      apply Qmult_lt_l. unfold Qlt. simpl. unfold Z.lt. auto.
      apply (Qle_lt_trans _ (Qabs (yn q)%nat * (1 # Ay))).
      rewrite <- (Qmult_comm (1 # Ay)). apply Qmult_le_compat_r.
      unfold Qle. simpl. rewrite Pos2Z.inj_max. apply Z.le_max_l.
      apply Qabs_nonneg. rewrite <- (Qmult_inv_r (1#Ay)).
      2: intro abs; inversion abs.
      rewrite Qmult_comm. apply Qmult_lt_l. reflexivity.
      setoid_replace (/(1#Ay))%Q with (Z.pos Ay # 1)%Q. 2: reflexivity.
      apply majy. refine (Pos.le_trans _ _ _ _ H0).
      rewrite <- Pos.max_assoc. apply Pos.le_max_l.
  - rewrite Qinv_plus_distr. unfold Qeq. reflexivity.
Qed.

Lemma linear_max : forall (p Ax Ay i : positive),
  Pos.le p i
  -> (Pos.max (Pos.max 2 (2 * Pos.max Ax Ay * p))
         (2 * Pos.max Ax Ay * p)
     <= (2 * Pos.max Ax Ay) * i)%positive.
Proof.
  intros. rewrite Pos.max_l. 2: apply Pos.le_max_r. rewrite Pos.max_r.
  apply Pos.mul_le_mono_l. exact H.
  apply (Pos.le_trans _ (2*1)). apply Pos.le_refl.
  rewrite <- Pos.mul_assoc, <- (Pos.mul_le_mono_l 2).
  destruct (Pos.max Ax Ay * p)%positive; discriminate.
Qed.

Definition CReal_mult (x y : CReal) : CReal.
Proof.
  destruct x as [xn limx]. destruct y as [yn limy].
  pose (QCauchySeq_bound xn id) as Ax.
  pose (QCauchySeq_bound yn id) as Ay.
  exists (fun n : positive => xn ((2 * Pos.max Ax Ay) * n)%positive
               * yn ((2 * Pos.max Ax Ay) * n)%positive).
  intros p n k H0 H1.
  apply (CReal_mult_cauchy xn xn yn Ax Ay id limx limy).
  intros. apply (QCauchySeq_bounded_prop xn id limx).
  apply (Pos.le_trans _ 2). discriminate. exact H.
  intros. exact (QCauchySeq_bounded_prop yn id limy _ H).
  apply linear_max; assumption. apply linear_max; assumption.
Defined.

Infix "*" := CReal_mult : CReal_scope.

Lemma CReal_mult_unfold : forall x y : CReal,
    QSeqEquivEx (proj1_sig (CReal_mult x y))
                (fun n : positive => proj1_sig x n * proj1_sig y n)%Q.
Proof.
  intros [xn limx] [yn limy]. unfold CReal_mult ; simpl.
  pose proof (QCauchySeq_bounded_prop xn id limx) as majx.
  pose proof (QCauchySeq_bounded_prop yn id limy) as majy.
  remember (QCauchySeq_bound xn id) as Ax.
  remember (QCauchySeq_bound yn id) as Ay.
  exists (fun p : positive =>
         Pos.max (2 * Pos.max Ax Ay * p)
           (2 * Pos.max Ax Ay * p)).
  intros p n k H0 H1. rewrite Pos.max_l in H0, H1.
  apply (CReal_mult_cauchy xn xn yn Ax Ay id limx limy).
  2: apply majy. intros. apply majx.
  refine (Pos.le_trans _ _ _ _ H). discriminate.
  3: apply Pos.le_refl. 3: apply Pos.le_refl.
  apply linear_max. refine (Pos.le_trans _ _ _ _ H0).
  apply (Pos.le_trans _ (1*p)). apply Pos.le_refl.
  apply Pos.mul_le_mono_r. discriminate.
  rewrite Pos.max_l.
  rewrite Pos.max_r. apply H1. 2: apply Pos.le_max_r.
  apply (Pos.le_trans _ (2*1)). apply Pos.le_refl. unfold id.
  rewrite <- Pos.mul_assoc, <- (Pos.mul_le_mono_l 2 1).
  destruct (Pos.max Ax Ay * p)%positive; discriminate.
Qed.

Lemma CReal_mult_assoc_bounded_r : forall (xn yn zn : positive -> Q),
    QSeqEquivEx xn yn (* both are Cauchy with same limit *)
    -> QSeqEquiv zn zn id
    -> QSeqEquivEx (fun n => xn n * zn n)%Q (fun n => yn n * zn n)%Q.
Proof.
  intros xn yn zn [cvmod cveq] H0.
  exists (fun p => Pos.max (Pos.max (cvmod 2%positive) (cvmod (2 * (Pos.max (QCauchySeq_bound yn (fun k : positive => cvmod (2 * k)%positive)) (QCauchySeq_bound zn id)) * p)%positive))
               (2 * (Pos.max (QCauchySeq_bound yn (fun k : positive => cvmod (2 * k)%positive)) (QCauchySeq_bound zn id)) * p)%positive).
  apply (CReal_mult_cauchy _ _ _ _ _ _ cveq H0).
  exact (QCauchySeq_bounded_prop
           yn (fun k => cvmod (2 * k)%positive)
           (QSeqEquiv_cau_r xn yn cvmod cveq)).
  exact (QCauchySeq_bounded_prop zn id H0).
Qed.

Lemma CReal_mult_assoc : forall x y z : CReal, (x * y) * z == x * (y * z).
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig y n * proj1_sig z n)%Q).
  - apply (QSeqEquivEx_trans _ (fun n => proj1_sig (CReal_mult x y) n * proj1_sig z n)%Q).
    apply CReal_mult_unfold.
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; unfold CReal_mult; simpl.
    pose proof (QCauchySeq_bounded_prop xn id limx) as majx.
    pose proof (QCauchySeq_bounded_prop yn id limy) as majy.
    pose proof (QCauchySeq_bounded_prop zn id limz) as majz.
    remember (QCauchySeq_bound xn id) as Ax.
    remember (QCauchySeq_bound yn id) as Ay.
    remember (QCauchySeq_bound zn id) as Az.
    apply CReal_mult_assoc_bounded_r. 2: exact limz.
    exists (fun p : positive =>
         Pos.max (2 * Pos.max Ax Ay * p)
                 (2 * Pos.max Ax Ay * p)).
    intros p n k H0 H1.
    apply (CReal_mult_cauchy xn xn yn Ax Ay id limx limy).
    2: exact majy. intros. apply majx. refine (Pos.le_trans _ _ _ _ H).
    discriminate. rewrite Pos.max_l in H0, H1.
    2: apply Pos.le_refl. 2: apply Pos.le_refl.
    apply linear_max.
    apply (Pos.le_trans _ (2 * Pos.max Ax Ay * p)).
    apply (Pos.le_trans _ (1*p)). apply Pos.le_refl.
    apply Pos.mul_le_mono_r. discriminate.
    exact H0. rewrite Pos.max_l. 2: apply Pos.le_max_r.
    rewrite Pos.max_r in H1. 2: apply Pos.le_refl.
    refine (Pos.le_trans _ _ _ _ H1). rewrite Pos.max_r.
    apply Pos.le_refl. apply (Pos.le_trans _ (2*1)). apply Pos.le_refl.
    unfold id.
    rewrite <- Pos.mul_assoc, <- (Pos.mul_le_mono_l 2 1).
    destruct (Pos.max Ax Ay * p)%positive; discriminate.
  - apply (QSeqEquivEx_trans
             _ (fun n => proj1_sig x n * proj1_sig (CReal_mult y z) n)%Q).
    2: apply QSeqEquivEx_sym; apply CReal_mult_unfold.
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; unfold CReal_mult; simpl.
    pose proof (QCauchySeq_bounded_prop xn id limx) as majx.
    pose proof (QCauchySeq_bounded_prop yn id limy) as majy.
    pose proof (QCauchySeq_bounded_prop zn id limz) as majz.
    remember (QCauchySeq_bound xn id) as Ax.
    remember (QCauchySeq_bound yn id) as Ay.
    remember (QCauchySeq_bound zn id) as Az.
    pose proof (CReal_mult_assoc_bounded_r (fun n0 : positive => yn n0 * zn n0)%Q (fun n : positive =>
          yn ((Pos.max Ay Az)~0 * n)%positive
          * zn ((Pos.max Ay Az)~0 * n)%positive)%Q xn)
      as [cvmod cveq].
    + exists (fun p : positive =>
           Pos.max (2 * Pos.max Ay Az * p)
                   (2 * Pos.max Ay Az * p)).
      intros p n k H0 H1. rewrite Pos.max_l in H0, H1.
      apply (CReal_mult_cauchy yn yn zn Ay Az id limy limz).
      2: exact majz. intros. apply majy. refine (Pos.le_trans _ _ _ _ H).
      discriminate.
      3: apply Pos.le_refl. 3: apply Pos.le_refl.
      rewrite Pos.max_l. rewrite Pos.max_r. apply H0.
      apply (Pos.le_trans _ (2*1)). apply Pos.le_refl. unfold id.
      rewrite <- Pos.mul_assoc, <- (Pos.mul_le_mono_l 2 1).
      destruct (Pos.max Ay Az * p)%positive; discriminate.
      apply Pos.le_max_r.
      apply linear_max. refine (Pos.le_trans _ _ _ _ H1).
      apply (Pos.le_trans _ (1*p)). apply Pos.le_refl.
      apply Pos.mul_le_mono_r. discriminate.
    + exact limx.
    + exists cvmod. intros p k n H1 H2. specialize (cveq p k n H1 H2).
      setoid_replace (xn k * yn k * zn k -
                      xn n *
                      (yn ((Pos.max Ay Az)~0 * n)%positive *
                       zn ((Pos.max Ay Az)~0 * n)%positive))%Q
        with ((fun n : positive => yn n * zn n * xn n) k -
              (fun n : positive =>
                 yn ((Pos.max Ay Az)~0 * n)%positive *
                 zn ((Pos.max Ay Az)~0 * n)%positive *
                 xn n) n)%Q.
      apply cveq. ring.
Qed.

Lemma CReal_mult_comm : forall x y : CReal, x * y == y * x.
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig y n * proj1_sig x n)%Q).
  destruct x as [xn limx], y as [yn limy]; simpl.
  2: apply QSeqEquivEx_sym; apply CReal_mult_unfold.
  pose proof (QCauchySeq_bounded_prop xn id limx) as majx.
  pose proof (QCauchySeq_bounded_prop yn id limy) as majy.
  remember (QCauchySeq_bound xn id) as Ax.
  remember (QCauchySeq_bound yn id) as Ay.
  apply QSeqEquivEx_sym.
  exists (fun p : positive =>
       Pos.max (2 * Pos.max Ay Ax * p)
               (2 * Pos.max Ay Ax * p)).
  intros p n k H0 H1. rewrite Pos.max_l in H0, H1.
  2: apply Pos.le_refl. 2: apply Pos.le_refl.
  rewrite (Qmult_comm (xn ((Pos.max Ax Ay)~0 * k)%positive)).
  apply (CReal_mult_cauchy yn yn xn Ay Ax id limy limx).
  2: exact majx. intros. apply majy. refine (Pos.le_trans _ _ _ _ H).
  discriminate.
  rewrite Pos.max_l. rewrite Pos.max_r. apply H0.
  unfold id.
  apply (Pos.le_trans _ (2*1)). apply Pos.le_refl.
  rewrite <- Pos.mul_assoc, <- (Pos.mul_le_mono_l 2 1).
  destruct (Pos.max Ay Ax * p)%positive; discriminate.
  apply Pos.le_max_r. rewrite (Pos.max_comm Ax Ay).
  apply linear_max. refine (Pos.le_trans _ _ _ _ H1).
  apply (Pos.le_trans _ (1*p)). apply Pos.le_refl.
  apply Pos.mul_le_mono_r. discriminate.
Qed.

Lemma CReal_mult_proper_l : forall x y z : CReal,
    y == z -> x * y == x * z.
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig y n)%Q).
  apply CReal_mult_unfold.
  rewrite CRealEq_diff in H. rewrite <- CRealEq_modindep in H.
  apply QSeqEquivEx_sym.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig z n)%Q).
  apply CReal_mult_unfold.
  destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl.
  destruct H as [cvmod H]. simpl in H.
  pose proof (QCauchySeq_bounded_prop xn id limx) as majx.
  pose proof (QCauchySeq_bounded_prop
           zn (fun k => cvmod (2 * k)%positive)
           (QSeqEquiv_cau_r yn zn cvmod H)) as majz.
  remember (QCauchySeq_bound xn id) as Ax.
  remember (QCauchySeq_bound zn (fun k => cvmod (2 * k)%positive)) as Az.
  apply QSeqEquivEx_sym.
  exists (fun p : positive =>
       Pos.max (Pos.max (cvmod (2%positive)) (cvmod (2 * Pos.max Az Ax * p)%positive))
               (2 * Pos.max Az Ax * p)).
  intros p n k H1 H2.
  setoid_replace (xn n * yn n - xn k * zn k)%Q
    with (yn n * xn n - zn k * xn k)%Q. 2: ring.
  apply (CReal_mult_cauchy yn zn xn Az Ax cvmod H limx majz majx).
  exact H1. exact H2.
Qed.

Lemma CReal_mult_lt_0_compat : forall x y : CReal,
    inject_Q 0 < x
    -> inject_Q 0 < y
    -> inject_Q 0 < x * y.
Proof.
  intros. destruct H as [x0 H], H0 as [x1 H0].
  pose proof (CRealLt_aboveSig (inject_Q 0) x x0 H).
  pose proof (CRealLt_aboveSig (inject_Q 0) y x1 H0).
  destruct x as [xn limx], y as [yn limy]; simpl in H, H1, H2, H0.
  pose proof (QCauchySeq_bounded_prop xn id limx) as majx.
  pose proof (QCauchySeq_bounded_prop yn id limy) as majy.
  destruct (Qarchimedean (/ (xn x0 - 0 - (2 # x0)))).
  destruct (Qarchimedean (/ (yn x1 - 0 - (2 # x1)))).
  exists (Pos.max x0 x~0 * Pos.max x1 x2~0)%positive.
  simpl.
  remember (QCauchySeq_bound xn id) as Ax.
  remember (QCauchySeq_bound yn id) as Ay.
  unfold Qminus. rewrite Qplus_0_r.
  unfold Qminus in H1, H2.
  specialize (H1 ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive).
  assert (Pos.max x1 x2~0 <= (Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive.
  { rewrite Pos.mul_assoc.
    rewrite <- (Pos.mul_1_l (Pos.max x1 x2~0)).
    rewrite Pos.mul_assoc. apply Pos.mul_le_mono_r. discriminate. }
  specialize (H2 ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive H3).
  rewrite Qplus_0_r in H1, H2.
  apply (Qlt_trans _ ((2 # Pos.max x0 x~0) * (2 # Pos.max x1 x2~0))).
  unfold Qlt; simpl. assert (forall p : positive, (Z.pos p < Z.pos p~0)%Z).
  intro p. rewrite <- (Z.mul_1_l (Z.pos p)).
  replace (Z.pos p~0) with (2 * Z.pos p)%Z. apply Z.mul_lt_mono_pos_r.
  apply Pos2Z.is_pos. reflexivity. reflexivity.
  apply H4.
  apply (Qlt_trans _ ((2 # Pos.max x0 x~0) * (yn ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive))).
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
  2: apply QSeqEquivEx_sym; exists (fun p:positive => 2 * p)%positive
  ; apply CReal_plus_unfold.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n
                                    * (proj1_sig y n + proj1_sig z n))%Q).
  - pose proof (CReal_plus_unfold y z).
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl; simpl in H.
    pose proof (QCauchySeq_bounded_prop xn id) as majx.
    pose proof (QCauchySeq_bounded_prop yn id) as majy.
    pose proof (QCauchySeq_bounded_prop zn id) as majz.
    remember (QCauchySeq_bound xn id) as Ax.
    remember (QCauchySeq_bound yn id) as Ay.
    remember (QCauchySeq_bound zn id) as Az.
    pose proof (CReal_mult_cauchy (fun n => yn (n~0)%positive + zn (n~0)%positive)%Q
                                  (fun n => yn n + zn n)%Q
                                  xn (Ay + Az) Ax
                                  (fun p:positive => 2 * p)%positive H limx).
    exists (fun p : positive => (2 * (2 * Pos.max (Ay + Az) Ax * p))%positive).
    intros p n k H1 H2.
    setoid_replace (xn n * (yn (n~0)%positive + zn (n~0)%positive) - xn k * (yn k + zn k))%Q
      with ((yn (n~0)%positive + zn (n~0)%positive) * xn n - (yn k + zn k) * xn k)%Q.
    2: ring.
    assert ((2 * Pos.max (Ay + Az) Ax * p) <=
            2 * (2 * Pos.max (Ay + Az) Ax * p))%positive.
    { rewrite <- Pos.mul_assoc.
      apply Pos.mul_le_mono_l.
      apply (Pos.le_trans _ (1*(Pos.max (Ay + Az) Ax * p))).
      apply Pos.le_refl. apply Pos.mul_le_mono_r. discriminate. }
    apply H0. intros n0 H4.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle _ _)).
    rewrite Pos2Z.inj_add, <- Qinv_plus_distr. apply Qplus_lt_le_compat.
    apply majy. exact limy.
    refine (Pos.le_trans _ _ _ _ H4); discriminate.
    apply Qlt_le_weak. apply majz. exact limz.
    refine (Pos.le_trans _ _ _ _ H4); discriminate.
    apply majx. exact limx. refine (Pos.le_trans _ _ _ _ H1).
    rewrite Pos.max_l. rewrite Pos.max_r. apply Pos.le_refl.
    rewrite <- (Pos.mul_le_mono_l 2).
    apply (Pos.le_trans _ (2*1)). apply Pos.le_refl.
    rewrite <- Pos.mul_assoc, <- Pos.mul_le_mono_l.
    destruct (Pos.max (Ay + Az) Ax * p)%positive; discriminate.
    apply (Pos.le_trans _ (2 * (2 * Pos.max (Ay + Az) Ax * p))).
    2: apply Pos.le_max_r.
    rewrite <- Pos.mul_assoc. rewrite (Pos.mul_assoc 2 2).
    rewrite <- Pos.mul_le_mono_r. discriminate.
    refine (Pos.le_trans _ _ _ _ H2). rewrite <- Pos.max_comm.
    rewrite Pos.max_assoc. rewrite Pos.max_r. apply Pos.le_refl.
    apply Pos.max_lub. apply H3.
    rewrite <- Pos.mul_le_mono_l.
    apply (Pos.le_trans _ (2*1)). apply Pos.le_refl.
    rewrite <- Pos.mul_assoc, <- Pos.mul_le_mono_l.
    destruct (Pos.max (Ay + Az) Ax * p)%positive; discriminate.
  - destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl.
    pose proof (QCauchySeq_bounded_prop xn id) as majx.
    pose proof (QCauchySeq_bounded_prop yn id) as majy.
    pose proof (QCauchySeq_bounded_prop zn id) as majz.
    remember (QCauchySeq_bound xn id) as Ax.
    remember (QCauchySeq_bound yn id) as Ay.
    remember (QCauchySeq_bound zn id) as Az.
    exists (fun p : positive => (2 * (Pos.max (Pos.max Ax Ay) Az) * (2 * p))%positive).
    intros p n k H H0.
    setoid_replace (xn n * (yn n + zn n) -
     (xn ((Pos.max Ax Ay)~0 * k)%positive *
      yn ((Pos.max Ax Ay)~0 * k)%positive +
      xn ((Pos.max Ax Az)~0 * k)%positive *
      zn ((Pos.max Ax Az)~0 * k)%positive))%Q
      with (xn n * yn n - (xn ((Pos.max Ax Ay)~0 * k)%positive *
                           yn ((Pos.max Ax Ay)~0 * k)%positive)
            + (xn n * zn n - xn ((Pos.max Ax Az)~0 * k)%positive *
                             zn ((Pos.max Ax Az)~0 * k)%positive))%Q.
    2: ring.
    apply (Qle_lt_trans _ (Qabs (xn n * yn n - (xn ((Pos.max Ax Ay)~0 * k)%positive *
                                                yn ((Pos.max Ax Ay)~0 * k)%positive))
                           + Qabs (xn n * zn n - xn ((Pos.max Ax Az)~0 * k)%positive *
                             zn ((Pos.max Ax Az)~0 * k)%positive))).
    apply Qabs_triangle.
    setoid_replace (1#p)%Q with ((1#2*p) + (1#2*p))%Q.
    apply Qplus_lt_le_compat.
    + apply (CReal_mult_cauchy xn xn yn Ax Ay id limx limy).
      intros. apply majx. exact limx.
      refine (Pos.le_trans _ _ _ _ H1). discriminate.
      apply majy. exact limy.
      rewrite <- Pos.max_assoc.
      rewrite (Pos.max_l ((2 * Pos.max Ax Ay * (2 * p)))).
      2: apply Pos.le_refl.
      refine (Pos.le_trans _ _ _ _ H). apply Pos.max_lub.
      apply (Pos.le_trans _ (2*1)).
      apply Pos.le_refl. rewrite <- Pos.mul_assoc, <- Pos.mul_le_mono_l.
      destruct (Pos.max (Pos.max Ax Ay) Az * (2 * p))%positive; discriminate.
      rewrite <- Pos.mul_assoc, <- Pos.mul_assoc.
      rewrite <- Pos.mul_le_mono_l, <- Pos.mul_le_mono_r.
      apply Pos.le_max_l.
      rewrite <- Pos.max_assoc.
      rewrite (Pos.max_l ((2 * Pos.max Ax Ay * (2 * p)))).
      2: apply Pos.le_refl.
      rewrite Pos.max_r. apply (Pos.le_trans _ (1*k)).
      rewrite Pos.mul_1_l. refine (Pos.le_trans _ _ _ _ H0).
      rewrite <- Pos.mul_assoc, <- Pos.mul_assoc, <- Pos.mul_le_mono_l.
      rewrite <- Pos.mul_le_mono_r.
      apply Pos.le_max_l. apply Pos.mul_le_mono_r. discriminate.
      apply (Pos.le_trans _ (2*1)). apply Pos.le_refl.
      rewrite <- Pos.mul_assoc, <- Pos.mul_le_mono_l.
      destruct (Pos.max Ax Ay * (2 * p))%positive; discriminate.
    + apply Qlt_le_weak.
      apply (CReal_mult_cauchy xn xn zn Ax Az id limx limz).
      intros. apply majx. exact limx.
      refine (Pos.le_trans _ _ _ _ H1). discriminate.
      intros. apply majz. exact limz. exact H1.
      rewrite <- Pos.max_assoc.
      rewrite (Pos.max_l ((2 * Pos.max Ax Az * (2 * p)))).
      2: apply Pos.le_refl.
      refine (Pos.le_trans _ _ _ _ H). apply Pos.max_lub.
      apply (Pos.le_trans _ (2*1)).
      apply Pos.le_refl. rewrite <- Pos.mul_assoc, <- Pos.mul_le_mono_l.
      destruct (Pos.max (Pos.max Ax Ay) Az * (2 * p))%positive; discriminate.
      rewrite <- Pos.mul_assoc, <- Pos.mul_assoc.
      rewrite <- Pos.mul_le_mono_l, <- Pos.mul_le_mono_r.
      rewrite <- Pos.max_assoc, (Pos.max_comm Ay Az), Pos.max_assoc.
      apply Pos.le_max_l.
      rewrite <- Pos.max_assoc.
      rewrite (Pos.max_l ((2 * Pos.max Ax Az * (2 * p)))).
      2: apply Pos.le_refl.
      rewrite Pos.max_r. apply (Pos.le_trans _ (1*k)).
      rewrite Pos.mul_1_l. refine (Pos.le_trans _ _ _ _ H0).
      rewrite <- Pos.mul_assoc, <- Pos.mul_assoc, <- Pos.mul_le_mono_l.
      rewrite <- Pos.mul_le_mono_r.
      rewrite <- Pos.max_assoc, (Pos.max_comm Ay Az), Pos.max_assoc.
      apply Pos.le_max_l. apply Pos.mul_le_mono_r. discriminate.
      apply (Pos.le_trans _ (2*1)). apply Pos.le_refl.
      rewrite <- Pos.mul_assoc, <- Pos.mul_le_mono_l.
      destruct (Pos.max Ax Az * (2 * p))%positive; discriminate.
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
    rewrite Qmult_1_l in maj.
    pose proof (QCauchySeq_bounded_prop (fun _ : positive => 1%Q) id (ConstCauchy 1)).
    pose proof (QCauchySeq_bounded_prop rn id limr).
    remember (QCauchySeq_bound (fun _ : positive => 1%Q) id) as x.
    remember (QCauchySeq_bound rn id) as x0.
    specialize (limr m).
    apply (Qlt_not_le (2 # m) (1 # m)).
    apply (Qlt_trans _ (rn m
                        - rn ((Pos.max x x0)~0 * m)%positive)).
    apply maj.
    apply (Qle_lt_trans _ (Qabs (rn m - rn ((Pos.max x x0)~0 * m)%positive))).
    apply Qle_Qabs. apply limr. apply Pos.le_refl.
    rewrite <- (Pos.mul_1_l m). rewrite Pos.mul_assoc. unfold id.
    apply Pos.mul_le_mono_r. discriminate.
    apply Z.mul_le_mono_nonneg. discriminate. discriminate.
    discriminate. apply Z.le_refl.
  - intros [m maj]. simpl in maj.
    pose proof (QCauchySeq_bounded_prop (fun _ : positive => 1%Q) id (ConstCauchy 1)).
    pose proof (QCauchySeq_bounded_prop rn id limr).
    remember (QCauchySeq_bound (fun _ : positive => 1%Q) id) as x.
    remember (QCauchySeq_bound rn id) as x0.
    simpl in maj. rewrite Qmult_1_l in maj.
    specialize (limr m).
    apply (Qlt_not_le (2 # m) (1 # m)).
    apply (Qlt_trans _ (rn ((Pos.max x x0)~0 * m)%positive - rn m)).
    apply maj.
    apply (Qle_lt_trans _ (Qabs (rn ((Pos.max x x0)~0 * m)%positive - rn m))).
    apply Qle_Qabs. apply limr.
    rewrite <- (Pos.mul_1_l m). rewrite Pos.mul_assoc. unfold id.
    apply Pos.mul_le_mono_r. discriminate.
    apply Pos.le_refl.
    apply Z.mul_le_mono_nonneg. discriminate. discriminate.
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
    Qlt (2#n) (Qabs (proj1_sig x n))
    -> 0 # x.
Proof.
  intros. destruct x as [xn xcau]. simpl in H.
  destruct (Qlt_le_dec 0 (xn n)).
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
  pose proof (Qlt_floor (xn 4%positive + (1#4))). unfold inject_Z in H.
  pose proof (Qfloor_le (xn 4%positive + (1#4))). unfold inject_Z in H0.
  remember (Qfloor (xn 4%positive + (1#4)))%Z as n.
  exists (n+1)%Z. split.
  - assert (Qlt 0 ((n + 1 # 1) - (xn 4%positive + (1 # 4)))) as epsPos.
    { unfold Qminus. rewrite <- Qlt_minus_iff. exact H. }
    destruct (Qarchimedean (/((1#2)*((n + 1 # 1) - (xn 4%positive + (1 # 4)))))) as [k kmaj].
    exists (Pos.max 4 k). simpl.
    apply (Qlt_trans _ ((n + 1 # 1) - (xn 4%positive + (1 # 4)))).
    + setoid_replace (Z.pos k # 1)%Q with (/(1#k))%Q in kmaj. 2: reflexivity.
      rewrite <- Qinv_lt_contravar in kmaj. 2: reflexivity.
      apply (Qle_lt_trans _ (2#k)).
      rewrite <- (Qmult_le_l _ _ (1#2)).
      setoid_replace ((1 # 2) * (2 # k))%Q with (1#k)%Q. 2: reflexivity.
      setoid_replace ((1 # 2) * (2 # Pos.max 4 k))%Q with (1#Pos.max 4 k)%Q.
      2: reflexivity.
      unfold Qle; simpl. apply Pos2Z.pos_le_pos. apply Pos.le_max_r.
      reflexivity.
      rewrite <- (Qmult_lt_l _ _ (1#2)).
      setoid_replace ((1 # 2) * (2 # k))%Q with (1#k)%Q. exact kmaj.
      reflexivity. reflexivity. rewrite <- (Qmult_0_r (1#2)).
      rewrite Qmult_lt_l. exact epsPos. reflexivity.
    + rewrite <- (Qplus_lt_r _ _ (xn (Pos.max 4 k) - (n + 1 # 1) + (1#4))).
      ring_simplify.
      apply (Qle_lt_trans _ (Qabs (xn (Pos.max 4 k) - xn 4%positive))).
      apply Qle_Qabs. apply limx.
      apply Pos.le_max_l. apply Pos.le_refl.
  - apply (CReal_plus_lt_reg_l (-(2))). ring_simplify.
    exists 4%positive. simpl.
    rewrite <- Qinv_plus_distr.
    rewrite <- (Qplus_lt_r _ _ ((n#1) - (1#2))). ring_simplify.
    apply (Qle_lt_trans _ (xn 4%positive + (1 # 4)) _ H0).
    unfold Pos.to_nat; simpl.
    rewrite <- (Qplus_lt_r _ _ (-xn 4%positive)). ring_simplify.
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
  (* Convert to nat to use indefinite description. *)
  assert (exists n : nat, n <> O /\
             (Qlt (2 # Pos.of_nat n) (proj1_sig b (Pos.of_nat n) - proj1_sig a (Pos.of_nat n))
              \/ Qlt (2 # Pos.of_nat n) (proj1_sig d (Pos.of_nat n) - proj1_sig c (Pos.of_nat n)))).
  { destruct H. destruct H as [n maj]. exists (Pos.to_nat n). split.
    intro abs. destruct (Pos2Nat.is_succ n). rewrite H in abs.
    inversion abs. left. rewrite Pos2Nat.id. apply maj.
    destruct H as [n maj]. exists (Pos.to_nat n). split.
    intro abs. destruct (Pos2Nat.is_succ n). rewrite H in abs.
    inversion abs. right. rewrite Pos2Nat.id. apply maj. }
  apply constructive_indefinite_ground_description_nat in H0.
  - destruct H0 as [n [nPos maj]].
    destruct (Qlt_le_dec (2 # Pos.of_nat n)
                         (proj1_sig b (Pos.of_nat n) - proj1_sig a (Pos.of_nat n))).
    left. exists (Pos.of_nat n). apply q.
    assert (2 # Pos.of_nat n < proj1_sig d (Pos.of_nat n) - proj1_sig c (Pos.of_nat n))%Q.
    destruct maj. exfalso.
    apply (Qlt_not_le (2 # Pos.of_nat n) (proj1_sig b (Pos.of_nat n) - proj1_sig a (Pos.of_nat n))); assumption.
    assumption. clear maj. right. exists (Pos.of_nat n).
    apply H0.
  - clear H0. clear H. intro n. destruct n. right.
    intros [abs _]. exact (abs (eq_refl O)).
    destruct (Qlt_le_dec (2 # Pos.of_nat (S n)) (proj1_sig b (Pos.of_nat (S n)) - proj1_sig a (Pos.of_nat (S n)))).
    left. split. discriminate. left. apply q.
    destruct (Qlt_le_dec (2 # Pos.of_nat (S n)) (proj1_sig d (Pos.of_nat (S n)) - proj1_sig c (Pos.of_nat (S n)))).
    left. split. discriminate. right. apply q0.
    right. intros [_ [abs|abs]].
    apply (Qlt_not_le (2 # Pos.of_nat (S n))
                      (proj1_sig b (Pos.of_nat (S n)) - proj1_sig a (Pos.of_nat (S n)))); assumption.
    apply (Qlt_not_le (2 # Pos.of_nat (S n))
                      (proj1_sig d (Pos.of_nat (S n)) - proj1_sig c (Pos.of_nat (S n)))); assumption.
Qed.

Lemma CRealShiftReal : forall (x : CReal) (k : positive),
    QCauchySeq (fun n => proj1_sig x (Pos.add n k)) id.
Proof.
  assert (forall p k : positive, (p <= p + k)%positive).
  { intros. apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_add.
    apply (le_trans _ (Pos.to_nat p + 0)).
    rewrite plus_0_r. apply le_refl. apply Nat.add_le_mono_l.
    apply le_0_n. }
  intros x k n p q H0 H1.
  destruct x as [xn cau]; unfold proj1_sig.
  apply cau. apply (Pos.le_trans _ _ _ H0). apply H.
  apply (Pos.le_trans _ _ _ H1). apply H.
Qed.

Lemma CRealShiftEqual : forall (x : CReal) (k : positive),
    CRealEq x (exist _ (fun n => proj1_sig x (Pos.add n k)) (CRealShiftReal x k)).
Proof.
  intros. split.
  - intros [n maj]. destruct x as [xn cau]; simpl in maj.
    specialize (cau n (n + k)%positive n).
    apply Qlt_not_le in maj. apply maj. clear maj.
    apply (Qle_trans _ (Qabs (xn (n + k)%positive - xn n))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Zlt_le_weak.
    apply cau. unfold id. apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_add.
    apply (le_trans _ (Pos.to_nat n + 0)).
    rewrite plus_0_r. apply le_refl. apply Nat.add_le_mono_l.
    apply le_0_n. apply Pos.le_refl.
    apply Z.mul_le_mono_pos_r. apply Pos2Z.is_pos. discriminate.
  - intros [n maj]. destruct x as [xn cau]; simpl in maj.
    specialize (cau n n (n + k)%positive).
    apply Qlt_not_le in maj. apply maj. clear maj.
    apply (Qle_trans _ (Qabs (xn n - xn (n + k)%positive))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Zlt_le_weak.
    apply cau. apply Pos.le_refl.
    apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_add.
    apply (le_trans _ (Pos.to_nat n + 0)).
    rewrite plus_0_r. apply le_refl. apply Nat.add_le_mono_l.
    apply le_0_n.
    apply Z.mul_le_mono_pos_r. apply Pos2Z.is_pos. discriminate.
Qed.

(* Find an equal negative real number, which rational sequence
   stays below 0, so that it can be inversed. *)
Definition CRealNegShift (x : CReal)
  : x < inject_Q 0
    -> { y : prod positive CReal
      | x == (snd y) /\ forall n:positive, Qlt (proj1_sig (snd y) n) (-1 # fst y) }.
Proof.
  intro xNeg.
  pose proof (CRealLt_aboveSig x (inject_Q 0)).
  pose proof (CRealShiftReal x).
  pose proof (CRealShiftEqual x).
  destruct xNeg as [n maj], x as [xn cau]; simpl in maj.
  specialize (H n maj); simpl in H.
  destruct (Qarchimedean (/ (0 - xn n - (2 # n)))) as [a _].
  remember (Pos.max n a~0) as k.
  clear Heqk. clear maj. clear n.
  exists (pair k (exist _ (fun n => xn (Pos.add n k)) (H0 k))).
  split. apply H1. intro n. simpl. apply Qlt_minus_iff.
  apply (Qlt_trans _ (-(2 # k) - xn (n + k)%positive)).
  specialize (H (n + k)%positive).
  unfold Qminus in H. rewrite Qplus_0_l in H. apply Qlt_minus_iff in H.
  unfold Qminus. rewrite Qplus_comm. apply H. apply Pos2Nat.inj_le.
  rewrite <- (plus_0_l (Pos.to_nat k)). rewrite Pos2Nat.inj_add.
  apply Nat.add_le_mono_r. apply le_0_n.
  apply Qplus_lt_l.
  apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
  reflexivity.
Qed.

Definition CRealPosShift (x : CReal)
  : inject_Q 0 < x
    -> { y : prod positive CReal
      | x == (snd y) /\ forall n:positive, Qlt (1 # fst y) (proj1_sig (snd y) n) }.
Proof.
  intro xPos.
  pose proof (CRealLt_aboveSig (inject_Q 0) x).
  pose proof (CRealShiftReal x).
  pose proof (CRealShiftEqual x).
  destruct xPos as [n maj], x as [xn cau]; simpl in maj.
  simpl in H. specialize (H n).
  destruct (Qarchimedean (/ (xn n - 0 - (2 # n)))) as [a _].
  specialize (H maj); simpl in H.
  remember (Pos.max n a~0) as k.
  clear Heqk. clear maj. clear n.
  exists (pair k (exist _ (fun n => xn (Pos.add n k)) (H0 k))).
  split. apply H1. intro n. simpl. apply Qlt_minus_iff.
  rewrite <- Qlt_minus_iff. apply (Qlt_trans _ (2 # k)).
  apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
  reflexivity. specialize (H (n + k)%positive).
  unfold Qminus in H. rewrite Qplus_0_r in H.
  apply H. apply Pos2Nat.inj_le.
  rewrite <- (plus_0_l (Pos.to_nat k)). rewrite Pos2Nat.inj_add.
  apply Nat.add_le_mono_r. apply le_0_n.
Qed.

Lemma CReal_inv_neg : forall (yn : positive -> Q) (k : positive),
    (QCauchySeq yn id)
    -> (forall n : positive, yn n < -1 # k)%Q
    -> QCauchySeq (fun n : positive => / yn (k ^ 2 * n)%positive) id.
Proof.
  (* Prove the inverse sequence is Cauchy *)
  intros yn k cau maj n p q H0 H1.
  setoid_replace (/ yn (k ^ 2 * p)%positive -
                  / yn (k ^ 2 * q)%positive)%Q
    with ((yn (k ^ 2 * q)%positive -
           yn (k ^ 2 * p)%positive)
            / (yn (k ^ 2 * q)%positive *
               yn (k ^ 2 * p)%positive)).
  + apply (Qle_lt_trans _ (Qabs (yn (k ^ 2 * q)%positive
                                 - yn (k ^ 2 * p)%positive)
                                / (1 # (k^2)))).
    assert (1 # k ^ 2
            < Qabs (yn (k ^ 2 * q)%positive * yn (k ^ 2 * p)%positive))%Q.
    { rewrite Qabs_Qmult. unfold "^"%positive; simpl.
      rewrite factorDenom. rewrite Pos.mul_1_r.
      apply (Qlt_trans _ ((1#k) * Qabs (yn (k * (k * 1) * p)%positive))).
      apply Qmult_lt_l. reflexivity. rewrite Qabs_neg.
      specialize (maj (k * (k * 1) * p)%positive).
      apply Qlt_minus_iff in maj. apply Qlt_minus_iff.
      rewrite Qplus_comm. setoid_replace (-(1#k))%Q with (-1 # k)%Q. apply maj.
      reflexivity. apply (Qle_trans _ (-1 # k)). apply Zlt_le_weak.
      apply maj. discriminate. rewrite Pos.mul_1_r.
      apply Qmult_lt_r. apply (Qlt_trans 0 (1#k)). reflexivity.
      rewrite Qabs_neg.
      specialize (maj (k * k * p)%positive).
      apply Qlt_minus_iff in maj. apply Qlt_minus_iff.
      rewrite Qplus_comm. setoid_replace (-(1#k))%Q with (-1 # k)%Q.
      apply maj. reflexivity. apply (Qle_trans _ (-1 # k)). apply Zlt_le_weak.
      apply maj. discriminate.
      rewrite Qabs_neg.
      specialize (maj (k * k * q)%positive).
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
                    (k ^ 2 * q)%positive
                    (k ^ 2 * p)%positive).
    apply Qlt_shift_div_r. reflexivity.
    apply (Qlt_le_trans _ (1 # n * k ^ 2)). apply cau.
    rewrite Pos.mul_comm.
    unfold "^"%positive. simpl.
    unfold id. rewrite Pos.mul_1_r.
    rewrite <- Pos.mul_le_mono_l. exact H1.
    unfold id. rewrite Pos.mul_comm.
    apply Pos.mul_le_mono_l. exact H0.
    rewrite factorDenom. apply Qle_refl.
  + field. split. intro abs.
    specialize (maj (k ^ 2 * p)%positive).
    rewrite abs in maj. inversion maj.
    intro abs.
    specialize (maj (k ^ 2 * q)%positive).
    rewrite abs in maj. inversion maj.
Qed.

Lemma CReal_inv_pos : forall (yn : positive -> Q) (k : positive),
    (QCauchySeq yn id)
    -> (forall n : positive, 1 # k < yn n)%Q
    -> QCauchySeq (fun n : positive => / yn (k ^ 2 * n)%positive) id.
Proof.
  intros yn k cau maj n p q H0 H1.
  setoid_replace (/ yn (k ^ 2 * p)%positive -
                  / yn (k ^ 2 * q)%positive)%Q
    with ((yn (k ^ 2 * q)%positive -
           yn (k ^ 2 * p)%positive)
            / (yn (k ^ 2 * q)%positive *
               yn (k ^ 2 * p)%positive)).
  + apply (Qle_lt_trans _ (Qabs (yn (k ^ 2 * q)%positive
                                 - yn (k ^ 2 * p)%positive)
                                / (1 # (k^2)))).
    assert (1 # k ^ 2
            < Qabs (yn (k ^ 2 * q)%positive * yn (k ^ 2 * p)%positive))%Q.
    { rewrite Qabs_Qmult. unfold "^"%positive; simpl.
      rewrite factorDenom. rewrite Pos.mul_1_r.
      apply (Qlt_trans _ ((1#k) * Qabs (yn (k * k * p)%positive))).
      apply Qmult_lt_l. reflexivity. rewrite Qabs_pos.
      specialize (maj (k * k * p)%positive).
      apply maj. apply (Qle_trans _ (1 # k)).
      discriminate. apply Zlt_le_weak. apply maj.
      apply Qmult_lt_r. apply (Qlt_trans 0 (1#k)). reflexivity.
      rewrite Qabs_pos.
      specialize (maj (k * k * p)%positive).
      apply maj. apply (Qle_trans _ (1 # k)). discriminate.
      apply Zlt_le_weak. apply maj.
      rewrite Qabs_pos.
      specialize (maj (k * k * q)%positive).
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
                    (k ^ 2 * q)%positive
                    (k ^ 2 * p)%positive).
    apply Qlt_shift_div_r. reflexivity.
    apply (Qlt_le_trans _ (1 # n * k ^ 2)). apply cau.
    rewrite Pos.mul_comm. unfold id.
    apply Pos.mul_le_mono_l. exact H1.
    unfold id. rewrite Pos.mul_comm.
    apply Pos.mul_le_mono_l. exact H0.
    rewrite factorDenom. apply Qle_refl.
  + field. split. intro abs.
    specialize (maj (k ^ 2 * p)%positive).
    rewrite abs in maj. inversion maj.
    intro abs.
    specialize (maj (k ^ 2 * q)%positive).
    rewrite abs in maj. inversion maj.
Qed.

Definition CReal_inv (x : CReal) (xnz : x # 0) : CReal.
Proof.
  destruct xnz as [xNeg | xPos].
  - destruct (CRealNegShift x xNeg) as [[k y] [_ maj]].
    destruct y as [yn cau]; unfold proj1_sig, snd, fst in maj.
    exists (fun n:positive => Qinv (yn (Pos.mul (k^2) n)%positive)).
    apply (CReal_inv_neg yn). apply cau. apply maj.
  - destruct (CRealPosShift x xPos) as [[k y] [_ maj]].
    destruct y as [yn cau]; unfold proj1_sig, snd, fst in maj.
    exists (fun n => Qinv (yn (Pos.mul (k^2) n))).
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
    destruct (Qarchimedean (rn 1%positive)) as [A majA].
    exists (2 * (A + 1))%positive. unfold Qminus. rewrite Qplus_0_r.
    rewrite <- (Qmult_1_l (Qinv (rn (k * (k * 1) * (2 * (A + 1)))%positive))).
    apply Qlt_shift_div_l. apply (Qlt_trans 0 (1#k)). reflexivity.
    apply maj. rewrite <- (Qmult_inv_r (Z.pos A + 1 # 1)).
    setoid_replace (2 # 2 * (A + 1))%Q with (Qinv (Z.pos A + 1 # 1)).
    2: reflexivity.
    rewrite Qmult_comm. apply Qmult_lt_r. reflexivity.
    rewrite Pos.mul_1_r.
    rewrite <- (Qplus_lt_l _ _ (- rn 1%positive)).
    apply (Qle_lt_trans _ (Qabs (rn (k * k * (2 * (A + 1)))%positive + - rn 1%positive))).
    apply Qle_Qabs. apply (Qlt_le_trans _ 1). apply cau.
    destruct (k * k * (2 * (A + 1)))%positive; discriminate.
    apply Pos.le_refl.
    rewrite <- Qinv_plus_distr. rewrite <- (Qplus_comm 1).
    rewrite <- Qplus_0_r. rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
    rewrite Qplus_le_r. rewrite Qplus_0_l. apply Qlt_le_weak.
    apply Qlt_minus_iff in majA. apply majA.
    intro abs. inversion abs.
Qed.

Lemma CReal_linear_shift : forall (x : CReal) (k : positive),
    QCauchySeq (fun n => proj1_sig x (k * n)%positive) id.
Proof.
  intros [xn limx] k p n m H H0. unfold proj1_sig.
  apply limx. apply (Pos.le_trans _ n). apply H.
  rewrite <- (Pos.mul_1_l n). rewrite Pos.mul_assoc.
  apply Pos.mul_le_mono_r. destruct (k*1)%positive; discriminate.
  apply (Pos.le_trans _ (1*m)). exact H0.
  apply Pos.mul_le_mono_r. destruct k; discriminate.
Qed.

Lemma CReal_linear_shift_eq : forall (x : CReal) (k : positive),
    CRealEq x
    (exist (fun n : positive -> Q => QCauchySeq n id)
           (fun n : positive => proj1_sig x (k * n)%positive) (CReal_linear_shift x k)).
Proof.
  intros. apply CRealEq_diff. intro n.
  destruct x as [xn limx]; unfold proj1_sig.
  specialize (limx n n (k * n)%positive).
  apply (Qle_trans _ (1 # n)). apply Qlt_le_weak. apply limx.
  apply Pos.le_refl. rewrite <- (Pos.mul_1_l n).
  rewrite Pos.mul_assoc. apply Pos.mul_le_mono_r.
  destruct (k*1)%positive; discriminate.
  apply Z.mul_le_mono_nonneg_r. discriminate. discriminate.
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
               return ((forall n : positive, proj1_sig s n < -1 # k) -> CReal) := rneg in
            fun maj0 : forall n : positive, yn n < -1 # k =>
            exist (fun x : positive -> Q => QCauchySeq x id)
              (fun n : positive => Qinv (yn (k * (k * 1) * n))%positive)
              (CReal_inv_neg yn k cau maj0)) maj) rneg)))%Q.
    + apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply req.
    + apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : positive, proj1_sig s n < -1 # k) -> CReal) := rneg in
            fun maj0 : forall n : positive, yn n < -1 # k =>
            exist (fun x : positive -> Q => QCauchySeq x id)
              (fun n : positive => Qinv (yn (k * (k * 1) * n)%positive))
              (CReal_inv_neg yn k cau maj0)) maj)
                                    (exist _ (fun n => proj1_sig rneg (k * (k * 1) * n)%positive) (CReal_linear_shift rneg _)))))%Q.
      apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply CReal_linear_shift_eq.
      destruct r as [rn limr], rneg as [rnn limneg]; simpl.
      pose proof (QCauchySeq_bounded_prop
                  (fun n : positive => Qinv (rnn (k * (k * 1) * n)%positive))
                  id (CReal_inv_neg rnn k limneg maj)).
      pose proof (QCauchySeq_bounded_prop
            (fun n : positive => rnn (k * (k * 1) * n)%positive)
            id
            (CReal_linear_shift
               (exist (fun x0 : positive -> Q => QCauchySeq x0 id) rnn limneg)
               (k * (k * 1)))) ; simpl.
      remember (QCauchySeq_bound
             (fun n0 : positive => / rnn (k * (k * 1) * n0)%positive)%Q
             id) as x.
      remember (QCauchySeq_bound
             (fun n0 : positive => rnn (k * (k * 1) * n0)%positive)
             id) as x0.
      exists (fun n => 1%positive). intros p n m H2 H3. rewrite Qmult_comm.
      rewrite Qmult_inv_r. unfold Qminus. rewrite Qplus_opp_r.
      reflexivity. intro abs.
      unfold snd,fst, proj1_sig in maj.
      specialize (maj (k * (k * 1) * (Pos.max x x0 * n)~0)%positive).
      rewrite abs in maj. inversion maj.
  - (* r > 0 *) destruct (CRealPosShift r c) as [[k rneg] [req maj]].
    simpl in req. apply CRealEq_diff. apply CRealEq_modindep.
    apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : positive, 1 # k < proj1_sig s n) -> CReal) := rneg in
            fun maj0 : forall n : positive, 1 # k < yn n =>
            exist (fun x : positive -> Q => QCauchySeq x id)
              (fun n : positive => Qinv (yn (k * (k * 1) * n)%positive))
              (CReal_inv_pos yn k cau maj0)) maj) rneg)))%Q.
    + apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply req.
    + assert (le 1 (Pos.to_nat k * (Pos.to_nat k * 1))%nat). rewrite mult_1_r.
      rewrite <- Pos2Nat.inj_mul. apply Pos2Nat.is_pos.
      apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : positive, 1 # k < proj1_sig s n) -> CReal) := rneg in
            fun maj0 : forall n : positive, 1 # k < yn n =>
            exist (fun x : positive -> Q => QCauchySeq x id)
              (fun n : positive => Qinv (yn (k * (k * 1) * n)%positive))
              (CReal_inv_pos yn k cau maj0)) maj)
                                    (exist _ (fun n => proj1_sig rneg (k * (k * 1) * n)%positive) (CReal_linear_shift rneg _)))))%Q.
      apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply CReal_linear_shift_eq.
      destruct r as [rn limr], rneg as [rnn limneg]; simpl.
      pose proof (QCauchySeq_bounded_prop
                  (fun n : positive => Qinv (rnn (k * (k * 1) * n)%positive))
                  id (CReal_inv_pos rnn k limneg maj)).
      pose proof (QCauchySeq_bounded_prop
            (fun n : positive => rnn (k * (k * 1) * n)%positive)
            id
            (CReal_linear_shift
               (exist (fun x0 : positive -> Q => QCauchySeq x0 id) rnn limneg)
               (k * (k * 1)))) ; simpl.
      remember (QCauchySeq_bound
             (fun n0 : positive => / rnn (k * (k * 1) * n0)%positive)
             id)%Q as x.
      remember (QCauchySeq_bound
             (fun n0 : positive => rnn (k * (k * 1) * n0)%positive)
             id) as x0.
      exists (fun n => 1%positive). intros p n m H2 H3. rewrite Qmult_comm.
      rewrite Qmult_inv_r. unfold Qminus. rewrite Qplus_opp_r.
      reflexivity. intro abs.
      specialize (maj ((k * (k * 1) * (Pos.max x x0 * n)~0)%positive)).
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
  destruct x as [xn xcau], y as [yn ycau].
  unfold CReal_mult, proj1_sig in kmaj.
  remember (QCauchySeq_bound xn id) as a.
  remember (QCauchySeq_bound yn id) as b.
  simpl in imaj, jmaj. simpl in H0.
  specialize (kmaj (Pos.max k (Pos.max i j)) (Pos.le_max_l _ _)).
  destruct (H0 (2*(Pos.max a b) * (Pos.max k (Pos.max i j)))%positive).
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
      rewrite <- (Qmult_1_l (Qabs (yn (2*(Pos.max a b) * Pos.max k (Pos.max i j))%positive))).
      apply (Qle_trans _ _ _ (Qle_Qabs _)). rewrite Qabs_Qmult.
      apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
      apply Qabs_Qle_condition. split.
      apply Qlt_le_weak. apply Qlt_minus_iff, (Qlt_trans _ (2#j)).
      reflexivity. apply jmaj.
      apply (Pos.le_trans _ (1 * Pos.max k (Pos.max i j))).
      rewrite Pos.mul_1_l.
      apply (Pos.le_trans _ (Pos.max i j) _ (Pos.le_max_r _ _)).
      apply Pos.le_max_r.
      rewrite <- Pos.mul_le_mono_r. discriminate.
      apply Qlt_le_weak. apply Qlt_minus_iff, (Qlt_trans _ (2#i)).
      reflexivity. apply imaj.
      apply (Pos.le_trans _ (1 * Pos.max k (Pos.max i j))).
      rewrite Pos.mul_1_l.
      apply (Pos.le_trans _ (Pos.max i j) _ (Pos.le_max_l _ _)).
      apply Pos.le_max_r.
      rewrite <- Pos.mul_le_mono_r. discriminate.
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
    CReal_inv (inject_Q (Z.pos b # 1)) (inr (CReal_injectQPos (Z.pos b # 1) pos))
    == inject_Q (1 # b).
Proof.
  intros.
  apply (CReal_mult_eq_reg_l (inject_Q (Z.pos b # 1))).
  - right. apply CReal_injectQPos. exact pos.
  - rewrite CReal_mult_comm, CReal_inv_l.
    apply CRealEq_diff. intro n. simpl.
    do 2 rewrite Pos.mul_1_r. rewrite Z.pos_sub_diag. discriminate.
Qed.

Definition CRealQ_dense (a b : CReal)
  : a < b -> { q : Q  &  a < inject_Q q < b }.
Proof.
  (* Locate a and b at the index given by a<b,
     and pick the middle rational number. *)
  intros [p pmaj].
  exists ((proj1_sig a p + proj1_sig b p) * (1#2))%Q.
  split.
  - apply (CReal_le_lt_trans _ _ _ (inject_Q_compare a p)). apply inject_Q_lt.
    apply (Qmult_lt_l _ _ 2). reflexivity.
    apply (Qplus_lt_l _ _ (-2*proj1_sig a p)).
    field_simplify. field_simplify in pmaj.
    setoid_replace (-2#2)%Q with (-1)%Q. 2: reflexivity.
    setoid_replace (2*(1#p))%Q with (2#p)%Q. 2: reflexivity.
    rewrite Qplus_comm. exact pmaj.
  - apply (CReal_plus_lt_reg_l (-b)).
    rewrite CReal_plus_opp_l.
    apply (CReal_plus_lt_reg_r
             (-inject_Q ((proj1_sig a p + proj1_sig b p) * (1 # 2)))).
    rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r, CReal_plus_0_l.
    rewrite <- opp_inject_Q.
    apply (CReal_le_lt_trans _ _ _ (inject_Q_compare (-b) p)). apply inject_Q_lt.
    apply (Qmult_lt_l _ _ 2). reflexivity.
    apply (Qplus_lt_l _ _ (2*proj1_sig b p)).
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
    simpl in maj. ring_simplify in maj. discriminate maj.
  - intros [n maj]. simpl in maj.
    simpl in maj. ring_simplify in maj. discriminate maj.
Qed.

Definition Rup_nat (x : CReal)
  : { n : nat & x < inject_Q (Z.of_nat n #1) }.
Proof.
  intros. destruct (CRealArchimedean x) as [p maj].
  destruct p.
  - exists O. apply maj.
  - exists (Pos.to_nat p). rewrite positive_nat_Z. apply maj.
  - exists O. apply (CReal_lt_trans _ (inject_Q (Z.neg p # 1))).
    apply maj. apply inject_Q_lt. reflexivity.
Qed.

Lemma CReal_mult_le_0_compat : forall (a b : CReal),
    0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  (* Limit of (a + 1/n)*b when n -> infty. *)
  intros. intro abs.
  assert (0 < -(a*b)) as epsPos.
  { rewrite <- CReal_opp_0. apply CReal_opp_gt_lt_contravar. exact abs. }
  destruct (Rup_nat (b * (/ (-(a*b))) (inr epsPos)))
    as [n maj].
  destruct n as [|n].
  - apply (CReal_mult_lt_compat_r (-(a*b))) in maj.
    rewrite CReal_mult_0_l, CReal_mult_assoc, CReal_inv_l, CReal_mult_1_r in maj.
    contradiction. exact epsPos.
  - (* n > 0 *)
    assert (0 < inject_Q (Z.of_nat (S n) #1)) as nPos.
    { apply inject_Q_lt. unfold Qlt, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. apply Z2Nat.inj_lt. discriminate.
      apply Zle_0_nat. rewrite Nat2Z.id. apply le_n_S, le_0_n. }
    assert (b * (/ inject_Q (Z.of_nat (S n) #1)) (inr nPos) < -(a*b)).
    { apply (CReal_mult_lt_reg_r (inject_Q (Z.of_nat (S n) #1))). apply nPos.
      rewrite CReal_mult_assoc, CReal_inv_l, CReal_mult_1_r.
      apply (CReal_mult_lt_compat_r (-(a*b))) in maj.
      rewrite CReal_mult_assoc, CReal_inv_l, CReal_mult_1_r in maj.
      rewrite CReal_mult_comm. apply maj. apply epsPos. }
    pose proof (CReal_mult_le_compat_l_half
                  (a + (/ inject_Q (Z.of_nat (S n) #1)) (inr nPos)) 0 b).
    assert (0 + 0 < a + (/ inject_Q (Z.of_nat (S n) #1)) (inr nPos)).
    { apply CReal_plus_le_lt_compat. apply H. apply CReal_inv_0_lt_compat. apply nPos. }
    rewrite CReal_plus_0_l in H3. specialize (H2 H3 H0).
    clear H3. rewrite CReal_mult_0_r in H2.
    apply H2. clear H2. rewrite CReal_mult_plus_distr_r.
    apply (CReal_plus_lt_compat_l (a*b)) in H1.
    rewrite CReal_plus_opp_r in H1.
    rewrite (CReal_mult_comm ((/ inject_Q (Z.of_nat (S n) #1)) (inr nPos))).
    apply H1.
Qed.

Lemma CReal_mult_le_compat_l : forall (r r1 r2:CReal),
    0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros. apply (CReal_plus_le_reg_r (-(r*r1))).
  rewrite CReal_plus_opp_r, CReal_opp_mult_distr_r.
  rewrite <- CReal_mult_plus_distr_l.
  apply CReal_mult_le_0_compat. exact H.
  apply (CReal_plus_le_reg_r r1).
  rewrite CReal_plus_0_l, CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_r.
  exact H0.
Qed.

Lemma CReal_mult_le_compat_r : forall (r r1 r2:CReal),
    0 <= r -> r1 <= r2 -> r1 * r <= r2 * r.
Proof.
  intros. apply (CReal_plus_le_reg_r (-(r1*r))).
  rewrite CReal_plus_opp_r, CReal_opp_mult_distr_l.
  rewrite <- CReal_mult_plus_distr_r.
  apply CReal_mult_le_0_compat. 2: exact H.
  apply (CReal_plus_le_reg_r r1). ring_simplify. exact H0.
Qed.

Lemma CReal_mult_le_reg_l :
  forall x y z : CReal,
    0 < x -> x * y <= x * z -> y <= z.
Proof.
  intros. intro abs.
  apply (CReal_mult_lt_compat_l x) in abs. contradiction.
  exact H.
Qed.

Lemma CReal_mult_le_reg_r :
  forall x y z : CReal,
    0 < x -> y * x <= z * x -> y <= z.
Proof.
  intros. intro abs.
  apply (CReal_mult_lt_compat_r x) in abs. contradiction.
  exact H.
Qed.
