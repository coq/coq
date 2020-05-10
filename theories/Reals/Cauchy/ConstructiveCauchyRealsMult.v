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

(** The multiplication and division of Cauchy reals.

    WARNING: this file is experimental and likely to change in future releases.
*)

Require Import QArith Qabs Qround.
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

Lemma QCauchySeq_bounded_prop (qn : positive -> Q)
  : QCauchySeq qn
    -> forall n:positive, Qlt (Qabs (qn n)) (Z.pos (QCauchySeq_bound qn id) # 1).
Proof.
  intros H n. unfold QCauchySeq_bound.
  assert (1 <= n)%positive as H0. { destruct n; discriminate. }
  specialize (H 1%positive (1%positive) n (Pos.le_refl _) H0).
  unfold id.
  destruct (qn (1%positive)) as [a b]. unfold Qnum.
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

Lemma factorDenom : forall (a:Z) (b d:positive), ((a # (d * b)) == (1#d) * (a#b))%Q.
Proof.
  intros. unfold Qeq. simpl. destruct a; reflexivity.
Qed.

Lemma CReal_mult_cauchy
  : forall (x y : CReal) (A : positive),
    (forall n : positive, (Qabs (proj1_sig x n) < Z.pos A # 1)%Q)
    -> (forall n : positive, (Qabs (proj1_sig y n) < Z.pos A # 1)%Q)
    -> QCauchySeq (fun n : positive => proj1_sig x (2 * A * n)%positive
                                   * proj1_sig y (2 * A * n)%positive).
Proof.
  intros [xn limx] [yn limy] A. unfold proj1_sig.
  intros majx majy k p q H H0.
  setoid_replace (xn (2*A*p)%positive * yn (2*A*p)%positive
                  - xn (2*A*q)%positive * yn (2*A*q)%positive)%Q
    with ((xn (2*A*p)%positive - xn (2*A*q)%positive) * yn (2*A*p)%positive
          + xn (2*A*q)%positive * (yn (2*A*p)%positive - yn (2*A*q)%positive))%Q.
  2: ring.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle _ _)).
  rewrite Qabs_Qmult, Qabs_Qmult.
  setoid_replace (1#k)%Q with ((1#2*k) + (1#2*k))%Q.
  2: rewrite Qinv_plus_distr; reflexivity.
  apply Qplus_lt_le_compat.
  - apply (Qle_lt_trans _ ((1#2*A * k) * Qabs (yn (2*A*p)%positive))).
    + apply Qmult_le_compat_r. apply Qlt_le_weak. apply limx.
      apply Pos.mul_le_mono_l, H. apply Pos.mul_le_mono_l, H0.
      apply Qabs_nonneg.
    + rewrite <- (Qmult_1_r (1 # 2 * k)).
      rewrite <- Pos.mul_assoc. rewrite <- (Pos.mul_comm k). rewrite Pos.mul_assoc.
      rewrite (factorDenom _ _ (2 * k)). rewrite <- Qmult_assoc.
      apply Qmult_lt_l. reflexivity.
      apply (Qle_lt_trans _ (Qabs (yn (2 * A * p)%positive) * (1 # A))).
      rewrite <- (Qmult_comm (1 # A)). apply Qmult_le_compat_r.
      unfold Qle. simpl. apply Z.le_refl.
      apply Qabs_nonneg. rewrite <- (Qmult_inv_r (1#A)).
      2: intro abs; inversion abs.
      rewrite Qmult_comm. apply Qmult_lt_l. reflexivity.
      setoid_replace (/(1#A))%Q with (Z.pos A # 1)%Q.
      2: reflexivity.
      apply majy.
  - apply (Qle_trans _ ((1 # 2 * A * k) * Qabs (xn (2*A*q)%positive))).
    + rewrite Qmult_comm. apply Qmult_le_compat_r.
      apply Qlt_le_weak. apply limy.
      apply Pos.mul_le_mono_l, H. apply Pos.mul_le_mono_l, H0.
      apply Qabs_nonneg.
    + rewrite <- (Qmult_1_r (1 # 2 * k)).
      rewrite <- Pos.mul_assoc. rewrite <- (Pos.mul_comm k). rewrite Pos.mul_assoc.
      rewrite (factorDenom _ _ (2 * k)). rewrite <- Qmult_assoc.
      apply Qlt_le_weak.
      apply Qmult_lt_l. reflexivity.
      apply (Qle_lt_trans _ (Qabs (xn (2 * A * q)%positive) * (1 # A))).
      rewrite <- (Qmult_comm (1 # A)). apply Qmult_le_compat_r.
      apply Qle_refl.
      apply Qabs_nonneg. rewrite <- (Qmult_inv_r (1#A)).
      2: intro abs; inversion abs.
      rewrite Qmult_comm. apply Qmult_lt_l. reflexivity.
      setoid_replace (/(1#A))%Q with (Z.pos A # 1)%Q. 2: reflexivity.
      apply majx.
Qed.

Definition CReal_mult (x y : CReal) : CReal.
Proof.
  exists (fun n : positive => proj1_sig x ((2 * Pos.max (QCauchySeq_bound (proj1_sig x) id) (QCauchySeq_bound (proj1_sig y) id)) * n)%positive
                                * proj1_sig y ((2 * Pos.max (QCauchySeq_bound (proj1_sig x) id)
                                                            (QCauchySeq_bound (proj1_sig y) id)) * n)%positive).
  apply (CReal_mult_cauchy x y).
  - intro n. destruct x as [xn caux]. unfold proj1_sig.
    pose proof (QCauchySeq_bounded_prop xn caux).
    apply (Qlt_le_trans _ (Z.pos (QCauchySeq_bound xn id) # 1)).
    apply H.
    unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    rewrite Pos2Z.inj_max. apply Z.le_max_l.
  - intro n. destruct y as [yn cauy]. unfold proj1_sig.
    pose proof (QCauchySeq_bounded_prop yn cauy).
    apply (Qlt_le_trans _ (Z.pos (QCauchySeq_bound yn id) # 1)).
    apply H.
    unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    rewrite Pos2Z.inj_max. apply Z.le_max_r.
Defined.

Infix "*" := CReal_mult : CReal_scope.

Lemma CReal_mult_comm : forall x y : CReal, x * y == y * x.
Proof.
  assert (forall x y : CReal, x * y <= y * x) as H.
  { intros x y [n nmaj]. apply (Qlt_not_le _ _ nmaj). clear nmaj.
    unfold CReal_mult, proj1_sig.
    destruct x as [xn limx], y as [yn limy].
    rewrite Pos.max_comm, Qmult_comm. ring_simplify. discriminate. }
  split; apply H.
Qed.

Lemma CReal_mult_proper_0_l : forall x y : CReal,
    y == 0 -> x * y == 0.
Proof.
  assert (forall a:Q, a-0 == a)%Q as Qmin0.
  { intros. ring. }
  intros. apply CRealEq_diff. intros n.
  destruct x as [xn limx], y as [yn limy].
  unfold CReal_mult, proj1_sig, inject_Q.
  rewrite CRealEq_diff in H; unfold proj1_sig, inject_Q in H.
  specialize (H (2 * Pos.max (QCauchySeq_bound xn id)
                             (QCauchySeq_bound yn id) * n))%positive.
  rewrite Qmin0 in H. rewrite Qmin0, Qabs_Qmult, Qmult_comm.
  apply (Qle_trans
           _ ((2 # (2 * Pos.max (QCauchySeq_bound xn id) (QCauchySeq_bound yn id) * n)%positive) *
       (Qabs (xn (2 * Pos.max (QCauchySeq_bound xn id) (QCauchySeq_bound yn id) * n)%positive) ))).
  apply Qmult_le_compat_r.
  2: apply Qabs_nonneg. exact H. clear H. rewrite Qmult_comm.
  apply (Qle_trans _ ((Z.pos (QCauchySeq_bound xn id) # 1)
                      * (2 # (2 * Pos.max (QCauchySeq_bound xn id) (QCauchySeq_bound yn id) * n)%positive))).
  apply Qmult_le_compat_r.
  apply Qlt_le_weak, (QCauchySeq_bounded_prop xn limx).
  discriminate.
  unfold Qle, Qmult, Qnum, Qden.
  rewrite Pos.mul_1_l. rewrite <- (Z.mul_comm 2), <- Z.mul_assoc.
  apply Z.mul_le_mono_nonneg_l. discriminate.
  rewrite <- Pos2Z.inj_mul. apply Pos2Z.pos_le_pos, Pos.mul_le_mono_r.
  apply (Pos.le_trans _ (2 * QCauchySeq_bound xn id)).
  apply (Pos.le_trans _ (1 * QCauchySeq_bound xn id)).
  apply Pos.le_refl. apply Pos.mul_le_mono_r. discriminate.
  apply Pos.mul_le_mono_l. apply Pos.le_max_l.
Qed.

Lemma CReal_mult_0_r : forall r, r * 0 == 0.
Proof.
  intros. apply CReal_mult_proper_0_l. reflexivity.
Qed.

Lemma CReal_mult_0_l : forall r, 0 * r == 0.
Proof.
  intros. rewrite CReal_mult_comm. apply CReal_mult_0_r.
Qed.

Lemma CRealLt_0_aboveSig : forall (x : CReal) (n : positive),
    Qlt (2 # n) (proj1_sig x n)
    -> forall p:positive,
      Pos.le n p -> Qlt (1 # n) (proj1_sig x p).
Proof.
  intros. destruct x as [xn caux].
  unfold proj1_sig. unfold proj1_sig in H.
  specialize (caux n n p (Pos.le_refl n) H0).
  apply (Qplus_lt_l _ _ (xn n-xn p)).
  apply (Qlt_trans _ ((1#n) + (1#n))).
  apply Qplus_lt_r. exact (Qle_lt_trans _ _ _ (Qle_Qabs _) caux).
  rewrite Qinv_plus_distr. ring_simplify. exact H.
Qed.

(* Correctness lemma for the Definition CReal_mult_lt_0_compat below. *)
Lemma CReal_mult_lt_0_compat_correct
  : forall (x y : CReal) (H : 0 < x) (H0 : 0 < y),
    (2 # 2 * proj1_sig H * proj1_sig H0 <
     proj1_sig (x * y)%CReal (2 * proj1_sig H * proj1_sig H0)%positive -
     proj1_sig (inject_Q 0) (2 * proj1_sig H * proj1_sig H0)%positive)%Q.
Proof.
  intros.
  destruct H as [x0 H], H0 as [x1 H0]. unfold proj1_sig.
  unfold inject_Q, proj1_sig, Qminus in H. rewrite Qplus_0_r in H.
  pose proof (CRealLt_0_aboveSig x x0 H) as H1.
  unfold inject_Q, proj1_sig, Qminus in H0. rewrite Qplus_0_r in H0.
  pose proof (CRealLt_0_aboveSig y x1 H0) as H2.
  destruct x as [xn limx], y as [yn limy]; simpl in H, H1, H2, H0.
  unfold CReal_mult, inject_Q, proj1_sig.
  remember (QCauchySeq_bound xn id) as Ax.
  remember (QCauchySeq_bound yn id) as Ay.
  unfold Qminus. rewrite Qplus_0_r.
  specialize (H2 (2 * (Pos.max Ax Ay) * (2 * x0 * x1))%positive).
  setoid_replace (2 # 2 * x0 * x1)%Q with ((1#x0) * (1#x1))%Q.
  assert (x0 <= 2 * Pos.max Ax Ay * (2 * x0 * x1))%positive.
  { apply (Pos.le_trans _ (2 * Pos.max Ax Ay * x0)).
    apply belowMultiple. apply Pos.mul_le_mono_l.
    rewrite (Pos.mul_comm 2 x0), <- Pos.mul_assoc, Pos.mul_comm.
    apply belowMultiple. }
  apply (Qlt_trans _ (xn (2 * Pos.max Ax Ay * (2 * x0 * x1))%positive * (1#x1))).
  - apply Qmult_lt_compat_r. reflexivity. apply H1, H3.
  - apply Qmult_lt_l.
    apply (Qlt_trans _ (1#x0)). reflexivity. apply H1, H3.
    apply H2. apply (Pos.le_trans _ (2 * Pos.max Ax Ay * x1)).
    apply belowMultiple. apply Pos.mul_le_mono_l. apply belowMultiple.
  - unfold Qeq, Qmult, Qnum, Qden.
    rewrite Z.mul_1_l, <- Pos2Z.inj_mul. reflexivity.
Qed.

(* Strict inequality on CReal is in sort Type, for example
   used in the computation of division. *)
Definition CReal_mult_lt_0_compat : forall x y : CReal,
    0 < x -> 0 < y -> 0 < x * y
  := fun x y H H0 => exist _ (2 * proj1_sig H * proj1_sig H0)%positive
                        (CReal_mult_lt_0_compat_correct
                           x y H H0).

Lemma CReal_mult_bound_indep
  : forall (x y : CReal) (A : positive)
      (xbound : forall n : positive, (Qabs (proj1_sig x n) < Z.pos A # 1)%Q)
      (ybound : forall n : positive, (Qabs (proj1_sig y n) < Z.pos A # 1)%Q),
    x * y == exist _
                   (fun n : positive => proj1_sig x (2 * A * n)%positive
                                     * proj1_sig y (2 * A * n)%positive)%Q
                   (CReal_mult_cauchy x y A xbound ybound).
Proof.
  intros. apply CRealEq_diff.
  pose proof (CReal_mult_cauchy x y) as xycau. intro n.
  destruct x as [xn caux], y as [yn cauy];
    unfold CReal_mult, CReal_plus, proj1_sig; unfold proj1_sig in xycau.
  pose proof (xycau A xbound ybound).
  remember (QCauchySeq_bound xn id) as Ax.
  remember (QCauchySeq_bound yn id) as Ay.
  remember (Pos.max Ax Ay) as B.
  setoid_replace (xn (2*B*n)%positive * yn (2*B*n)%positive
                  - xn (2*A*n)%positive * yn (2*A*n)%positive)%Q
    with ((xn (2*B*n)%positive - xn (2*A*n)%positive) * yn (2*B*n)%positive
          + xn (2*A*n)%positive * (yn (2*B*n)%positive - yn (2*A*n)%positive))%Q.
  2: ring.
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
  rewrite Qabs_Qmult, Qabs_Qmult.
  setoid_replace (2#n)%Q with ((1#n) + (1#n))%Q.
  2: rewrite Qinv_plus_distr; reflexivity.
  apply Qplus_le_compat.
  - apply (Qle_trans _ ((1#2*Pos.min A B * n) * Qabs (yn (2*B*n)%positive))).
    + apply Qmult_le_compat_r. apply Qlt_le_weak. apply caux.
      apply Pos.mul_le_mono_r, Pos.mul_le_mono_l, Pos.le_min_r.
      apply Pos.mul_le_mono_r, Pos.mul_le_mono_l, Pos.le_min_l.
      apply Qabs_nonneg.
    + unfold proj1_sig in ybound. clear xbound.
      apply (Qmult_le_l _ _ (Z.pos (2*Pos.min A B *n) # 1)).
      reflexivity. rewrite Qmult_assoc.
      setoid_replace ((Z.pos (2 * Pos.min A B * n) # 1) * (1 # 2 * Pos.min A B * n))%Q
        with 1%Q.
      rewrite Qmult_1_l.
      setoid_replace ((Z.pos (2 * Pos.min A B * n) # 1) * (1 # n))%Q
        with (Z.pos (2 * Pos.min A B) # 1)%Q.
      apply (Qle_trans _ (Z.pos (Pos.min A B) # 1)).
      destruct (Pos.lt_total A B). rewrite Pos.min_l.
      apply Qlt_le_weak, ybound. apply Pos.lt_le_incl, H0.
      destruct H0. rewrite Pos.min_l.
      apply Qlt_le_weak, ybound. rewrite H0. apply Pos.le_refl.
      rewrite Pos.min_r. subst B. apply (Qle_trans _ (Z.pos Ay #1)). subst Ay.
      apply Qlt_le_weak, (QCauchySeq_bounded_prop yn cauy).
      unfold Qle, Qnum, Qden.
      rewrite Z.mul_1_r, Z.mul_1_r, Pos2Z.inj_max. apply Z.le_max_r.
      apply Pos.lt_le_incl, H0.
      unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
      apply Pos2Z.pos_le_pos. apply belowMultiple.
      unfold Qeq, Qmult, Qnum, Qden.
      rewrite Z.mul_1_r, Z.mul_1_r, Pos2Z.inj_mul. reflexivity.
      unfold Qeq, Qmult, Qnum, Qden.
      rewrite Z.mul_1_r, Z.mul_1_r, Pos2Z.inj_mul. reflexivity.
  - rewrite Qmult_comm.
    apply (Qle_trans _ ((1#2*Pos.min A B * n) * Qabs (xn (2*A*n)%positive))).
    + apply Qmult_le_compat_r. apply Qlt_le_weak. apply cauy.
      apply Pos.mul_le_mono_r, Pos.mul_le_mono_l, Pos.le_min_r.
      apply Pos.mul_le_mono_r, Pos.mul_le_mono_l, Pos.le_min_l.
      apply Qabs_nonneg.
    + unfold proj1_sig in xbound. clear ybound.
      apply (Qmult_le_l _ _ (Z.pos (2*Pos.min A B *n) # 1)).
      reflexivity. rewrite Qmult_assoc.
      setoid_replace ((Z.pos (2 * Pos.min A B * n) # 1) * (1 # 2 * Pos.min A B * n))%Q
        with 1%Q.
      rewrite Qmult_1_l.
      setoid_replace ((Z.pos (2 * Pos.min A B * n) # 1) * (1 # n))%Q
        with (Z.pos (2 * Pos.min A B) # 1)%Q.
      apply (Qle_trans _ (Z.pos (Pos.min A B) # 1)).
      destruct (Pos.lt_total A B). rewrite Pos.min_l.
      apply Qlt_le_weak, xbound. apply Pos.lt_le_incl, H0.
      destruct H0. rewrite Pos.min_l.
      apply Qlt_le_weak, xbound. rewrite H0. apply Pos.le_refl.
      rewrite Pos.min_r. subst B. apply (Qle_trans _ (Z.pos Ax #1)). subst Ax.
      apply Qlt_le_weak, (QCauchySeq_bounded_prop xn caux).
      unfold Qle, Qnum, Qden.
      rewrite Z.mul_1_r, Z.mul_1_r, Pos2Z.inj_max. apply Z.le_max_l.
      apply Pos.lt_le_incl, H0.
      unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
      apply Pos2Z.pos_le_pos. apply belowMultiple.
      unfold Qeq, Qmult, Qnum, Qden.
      rewrite Z.mul_1_r, Z.mul_1_r, Pos2Z.inj_mul. reflexivity.
      unfold Qeq, Qmult, Qnum, Qden.
      rewrite Z.mul_1_r, Z.mul_1_r, Pos2Z.inj_mul. reflexivity.
Qed.

Lemma CReal_mult_plus_distr_l : forall r1 r2 r3 : CReal,
    r1 * (r2 + r3) == (r1 * r2) + (r1 * r3).
Proof.
  (* Use same bound, max of the 3 bounds for every product. *)
  intros x y z.
  remember (QCauchySeq_bound (proj1_sig x) id) as Ax.
  remember (QCauchySeq_bound (proj1_sig y) id) as Ay.
  remember (QCauchySeq_bound (proj1_sig z) id) as Az.
  pose (Pos.max Ax (Pos.add Ay Az)) as B.
  assert (forall n : positive, (Qabs (proj1_sig x n) < Z.pos B # 1)%Q) as xbound.
  { intro n. subst B. apply (Qlt_le_trans _ (Z.pos Ax #1)).
    rewrite HeqAx.
    apply (QCauchySeq_bounded_prop (proj1_sig x)).
    destruct x. exact q.
    unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Z.pos_le_pos. apply Pos.le_max_l. }
  assert (forall n : positive, (Qlt (Qabs (proj1_sig (y+z) n)) (Z.pos B # 1)))
    as sumbound.
  { intro n. destruct y as [yn cauy], z as [zn cauz].
    unfold CReal_plus, proj1_sig. rewrite Qred_correct.
    subst B. apply (Qlt_le_trans _ ((Z.pos Ay#1) + (Z.pos Az#1))).
    apply (Qle_lt_trans _ _ _ (Qabs_triangle _ _)).
    apply Qplus_lt_le_compat. rewrite HeqAy.
    unfold proj1_sig. apply (QCauchySeq_bounded_prop yn cauy).
    rewrite HeqAz.
    unfold proj1_sig. apply Qlt_le_weak, (QCauchySeq_bounded_prop zn cauz).
    unfold Qplus, Qle, Qnum, Qden.
    apply Pos2Z.pos_le_pos. simpl. repeat rewrite Pos.mul_1_r.
    apply Pos.le_max_r. }
  rewrite (CReal_mult_bound_indep x (y+z) B xbound sumbound).
  assert (forall n : positive, (Qabs (proj1_sig y n) < Z.pos B # 1)%Q) as ybound.
  { intro n. subst B. apply (Qlt_le_trans _ (Z.pos Ay #1)).
    rewrite HeqAy.
    apply (QCauchySeq_bounded_prop (proj1_sig y)).
    destruct y; exact q.
    unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Z.pos_le_pos. apply (Pos.le_trans _ (Ay + Az)).
    apply Pos2Nat.inj_le. rewrite <- (Nat.add_0_r (Pos.to_nat Ay)).
    rewrite Pos2Nat.inj_add. apply Nat.add_le_mono_l, le_0_n.
    apply Pos.le_max_r. }
  rewrite (CReal_mult_bound_indep x y B xbound ybound).
  assert (forall n : positive, (Qabs (proj1_sig z n) < Z.pos B # 1)%Q) as zbound.
  { intro n. subst B. apply (Qlt_le_trans _ (Z.pos Az #1)).
    rewrite HeqAz.
    apply (QCauchySeq_bounded_prop (proj1_sig z)).
    destruct z; exact q.
    unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Z.pos_le_pos. apply (Pos.le_trans _ (Ay + Az)).
    apply Pos2Nat.inj_le. rewrite <- (Nat.add_0_l (Pos.to_nat Az)).
    rewrite Pos2Nat.inj_add. apply Nat.add_le_mono_r, le_0_n.
    apply Pos.le_max_r. }
  rewrite (CReal_mult_bound_indep x z B xbound zbound).
  apply CRealEq_diff.
  pose proof (CReal_mult_cauchy x y) as xycau. intro n.
  destruct x as [xn caux], y as [yn cauy], z as [zn cauz];
    unfold CReal_mult, CReal_plus, proj1_sig; unfold proj1_sig in xycau.
  rewrite Qred_correct, Qred_correct.
  assert (forall a b c d e : Q,
             c * (d + e) - (a+b) == c*d-a + (c*e-b))%Q.
  { intros. ring. }
  rewrite H. clear H.
  setoid_replace (2#n)%Q with ((1#n) + (1#n))%Q.
  2: rewrite Qinv_plus_distr; reflexivity.
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
  apply Qplus_le_compat.
  - rewrite Qabs_Qminus.
    replace (2 * B * (2 * n))%positive with (2 * (2 * B * n))%positive.
    setoid_replace (xn (2 * (2 * B * n))%positive * yn (2 * (2 * B * n))%positive -
                    xn (2 * B * n)%positive * yn (2 * (2 * B * n))%positive)%Q
      with ((xn (2 * (2 * B * n))%positive - xn (2 * B * n)%positive)
            * yn (2 * (2 * B * n))%positive)%Q.
    2: ring. rewrite Qabs_Qmult.
    apply (Qle_trans _ ((1 # 2*B*n) * Qabs (yn (2 * (2 * B * n))%positive))).
    apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
    apply Qlt_le_weak, caux. apply belowMultiple. apply Pos.le_refl.
    apply (Qmult_le_l _ _ (Z.pos (2* B *n) # 1)).
    reflexivity. rewrite Qmult_assoc.
    setoid_replace ((Z.pos (2 * B * n) # 1) * (1 # 2 * B * n))%Q
      with 1%Q.
    rewrite Qmult_1_l.
    setoid_replace ((Z.pos (2 * B * n) # 1) * (1 # n))%Q
      with (Z.pos (2 * B) # 1)%Q.
    apply (Qle_trans _ (Z.pos B # 1)).
    apply Qlt_le_weak, ybound.
    unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Z.pos_le_pos. apply belowMultiple.
    unfold Qeq, Qmult, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    rewrite Pos2Z.inj_mul. reflexivity.
    unfold Qeq, Qmult, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    rewrite Pos2Z.inj_mul. reflexivity.
    rewrite <- (Pos.mul_assoc 2 B (2*n)%positive).
    apply f_equal. rewrite Pos.mul_assoc, (Pos.mul_comm 2 B). reflexivity.
  - rewrite Qabs_Qminus.
    replace (2 * B * (2 * n))%positive with (2 * (2 * B * n))%positive.
    setoid_replace (xn (2 * (2 * B * n))%positive * zn (2 * (2 * B * n))%positive -
                    xn (2 * B * n)%positive * zn (2 * (2 * B * n))%positive)%Q
      with ((xn (2 * (2 * B * n))%positive - xn (2 * B * n)%positive)
            * zn (2 * (2 * B * n))%positive)%Q.
    2: ring. rewrite Qabs_Qmult.
    apply (Qle_trans _ ((1 # 2*B*n) * Qabs (zn (2 * (2 * B * n))%positive))).
    apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
    apply Qlt_le_weak, caux. apply belowMultiple. apply Pos.le_refl.
    apply (Qmult_le_l _ _ (Z.pos (2* B *n) # 1)).
    reflexivity. rewrite Qmult_assoc.
    setoid_replace ((Z.pos (2 * B * n) # 1) * (1 # 2 * B * n))%Q
      with 1%Q.
    rewrite Qmult_1_l.
    setoid_replace ((Z.pos (2 * B * n) # 1) * (1 # n))%Q
      with (Z.pos (2 * B) # 1)%Q.
    apply (Qle_trans _ (Z.pos B # 1)).
    apply Qlt_le_weak, zbound.
    unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Z.pos_le_pos. apply belowMultiple.
    unfold Qeq, Qmult, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    rewrite Pos2Z.inj_mul. reflexivity.
    unfold Qeq, Qmult, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    rewrite Pos2Z.inj_mul. reflexivity.
    rewrite <- (Pos.mul_assoc 2 B (2*n)%positive).
    apply f_equal. rewrite Pos.mul_assoc, (Pos.mul_comm 2 B). reflexivity.
Qed.

Lemma CReal_mult_plus_distr_r : forall r1 r2 r3 : CReal,
    (r2 + r3) * r1 == (r2 * r1) + (r3 * r1).
Proof.
  intros.
  rewrite CReal_mult_comm, CReal_mult_plus_distr_l,
  <- (CReal_mult_comm r1), <- (CReal_mult_comm r1).
  reflexivity.
Qed.

Lemma CReal_opp_mult_distr_r
  : forall r1 r2 : CReal, - (r1 * r2) == r1 * (- r2).
Proof.
  intros. apply (CReal_plus_eq_reg_l (r1*r2)).
  rewrite CReal_plus_opp_r, <- CReal_mult_plus_distr_l.
  symmetry. apply CReal_mult_proper_0_l.
  apply CReal_plus_opp_r.
Qed.

Lemma CReal_mult_proper_l : forall x y z : CReal,
    y == z -> x * y == x * z.
Proof.
  intros. apply (CReal_plus_eq_reg_l (-(x*z))).
  rewrite CReal_plus_opp_l, CReal_opp_mult_distr_r.
  rewrite <- CReal_mult_plus_distr_l.
  apply CReal_mult_proper_0_l. rewrite H. apply CReal_plus_opp_l.
Qed.

Lemma CReal_mult_proper_r : forall x y z : CReal,
    y == z -> y * x == z * x.
Proof.
  intros. rewrite CReal_mult_comm, (CReal_mult_comm z).
  apply CReal_mult_proper_l, H.
Qed.

Lemma CReal_mult_assoc : forall x y z : CReal, (x * y) * z == x * (y * z).
Proof.
  intros.
  remember (QCauchySeq_bound (proj1_sig x) id) as Ax.
  remember (QCauchySeq_bound (proj1_sig y) id) as Ay.
  remember (QCauchySeq_bound (proj1_sig z) id) as Az.
  pose (Pos.add (Ax * Ay) (Ay * Az)) as B.
  assert (forall n : positive, (Qabs (proj1_sig x n) < Z.pos B # 1)%Q) as xbound.
  { intro n.
    destruct x as [xn limx]; unfold CReal_mult, proj1_sig.
    apply (Qlt_le_trans _ (Z.pos Ax#1)).
    rewrite HeqAx.
    apply (QCauchySeq_bounded_prop xn limx).
    subst B. unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Z.pos_le_pos. apply (Pos.le_trans _ (Ax*Ay)).
    rewrite Pos.mul_comm. apply belowMultiple.
    apply Pos.lt_le_incl, Pos.lt_add_r. }
  assert (forall n : positive, (Qabs (proj1_sig y n) < Z.pos B # 1)%Q) as ybound.
  { intro n.
    destruct y as [xn limx]; unfold CReal_mult, proj1_sig.
    apply (Qlt_le_trans _ (Z.pos Ay#1)).
    rewrite HeqAy.
    apply (QCauchySeq_bounded_prop xn limx).
    subst B. unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Z.pos_le_pos. apply (Pos.le_trans _ (Ax*Ay)).
    apply belowMultiple. apply Pos.lt_le_incl, Pos.lt_add_r. }
  assert (forall n : positive, (Qabs (proj1_sig z n) < Z.pos B # 1)%Q) as zbound.
  { intro n.
    destruct z as [xn limx]; unfold CReal_mult, proj1_sig.
    apply (Qlt_le_trans _ (Z.pos Az#1)).
    rewrite HeqAz.
    apply (QCauchySeq_bounded_prop xn limx).
    subst B. unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Z.pos_le_pos. apply (Pos.le_trans _ (Ay*Az)).
    apply belowMultiple. rewrite Pos.add_comm.
    apply Pos.lt_le_incl, Pos.lt_add_r. }
  pose (exist (fun x0 : positive -> Q => QCauchySeq x0)
    (fun n : positive =>
     (proj1_sig x (2 * B * n)%positive * proj1_sig y (2 * B * n)%positive)%Q)
    (CReal_mult_cauchy x y B xbound ybound)) as xy.
  rewrite (CReal_mult_proper_r
             z (x*y) xy
             (CReal_mult_bound_indep x y B xbound ybound)).
  pose (exist (fun x0 : positive -> Q => QCauchySeq x0)
    (fun n : positive =>
     (proj1_sig y (2 * B * n)%positive * proj1_sig z (2 * B * n)%positive)%Q)
    (CReal_mult_cauchy y z B ybound zbound)) as yz.
  rewrite (CReal_mult_proper_l
             x (y*z) yz
             (CReal_mult_bound_indep y z B ybound zbound)).
  assert (forall n : positive, (Qabs (proj1_sig xy n) < Z.pos B # 1)%Q) as xybound.
  { intro n. unfold xy, proj1_sig. clear xy yz.
    destruct x as [xn limx], y as [yn limy]; unfold CReal_mult, proj1_sig.
    rewrite Qabs_Qmult.
    apply (Qle_lt_trans _ ((Z.pos Ax#1) * (Qabs (yn (2 * B * n)%positive)))).
    apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
    rewrite HeqAx.
    apply Qlt_le_weak, (QCauchySeq_bounded_prop xn limx).
    rewrite Qmult_comm.
    apply (Qle_lt_trans _ ((Z.pos Ay#1) * (Z.pos Ax#1))).
    apply Qmult_le_compat_r. 2: discriminate. rewrite HeqAy.
    apply Qlt_le_weak, (QCauchySeq_bounded_prop yn limy).
    subst B. unfold Qmult, Qlt, Qnum, Qden.
    rewrite Pos.mul_1_r, Z.mul_1_r, Z.mul_1_r, <- Pos2Z.inj_mul.
    apply Pos2Z.pos_lt_pos. rewrite Pos.mul_comm. apply Pos.lt_add_r. }
  rewrite (CReal_mult_bound_indep _ z B xybound zbound).
  assert (forall n : positive, (Qabs (proj1_sig yz n) < Z.pos B # 1)%Q) as yzbound.
  { intro n. unfold yz, proj1_sig. clear xybound xy yz.
    destruct z as [zn limz], y as [yn limy]; unfold CReal_mult, proj1_sig.
    rewrite Qabs_Qmult.
    apply (Qle_lt_trans _ ((Z.pos Ay#1) * (Qabs (zn (2 * B * n)%positive)))).
    apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
    rewrite HeqAy.
    apply Qlt_le_weak, (QCauchySeq_bounded_prop yn limy).
    rewrite Qmult_comm.
    apply (Qle_lt_trans _ ((Z.pos Az#1) * (Z.pos Ay#1))).
    apply Qmult_le_compat_r. 2: discriminate. rewrite HeqAz.
    apply Qlt_le_weak, (QCauchySeq_bounded_prop zn limz).
    subst B. unfold Qmult, Qlt, Qnum, Qden.
    rewrite Pos.mul_1_r, Z.mul_1_r, Z.mul_1_r, <- Pos2Z.inj_mul.
    apply Pos2Z.pos_lt_pos. rewrite Pos.add_comm, Pos.mul_comm.
    apply Pos.lt_add_r. }
  rewrite (CReal_mult_bound_indep x yz B xbound yzbound).
  apply CRealEq_diff. intro n. unfold proj1_sig, xy, yz.
  destruct x as [xn limx], y as [yn limy], z as [zn limz];
    unfold CReal_mult, proj1_sig.
  clear xybound yzbound xy yz.
  assert (forall a b c d e : Q, a*b*c - d*(b*e) == b*(a*c - d*e))%Q.
  { intros. ring. }
  rewrite H. clear H. rewrite Qabs_Qmult, Qmult_comm.
  setoid_replace (xn (2 * B * (2 * B * n))%positive * zn (2 * B * n)%positive -
                  xn (2 * B * n)%positive * zn (2 * B * (2 * B * n))%positive)%Q
    with ((xn (2 * B * (2 * B * n))%positive - xn (2 * B * n)%positive)
          * zn (2 * B * n)%positive
          + xn (2 * B * n)%positive *
            (zn (2*B*n)%positive - zn (2 * B * (2 * B * n))%positive))%Q.
  2: ring.
  apply (Qle_trans _ ( (Qabs ((1 # (2 * B * n)) * zn (2 * B * n)%positive)
                        + Qabs (xn (2 * B * n)%positive * (1 # (2 * B * n))))
        * Qabs (yn (2 * B * (2 * B * n))%positive))).
  apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
  apply Qplus_le_compat.
  rewrite Qabs_Qmult, Qabs_Qmult.
  apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
  apply Qlt_le_weak, limx. apply belowMultiple. apply Pos.le_refl.
  rewrite Qabs_Qmult, Qabs_Qmult, Qmult_comm, <- (Qmult_comm (Qabs (1 # 2 * B * n))).
  apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
  apply Qlt_le_weak, limz. apply Pos.le_refl. apply belowMultiple.
  rewrite Qabs_Qmult, Qabs_Qmult.
  rewrite (Qmult_comm (Qabs (1 # 2 * B * n))).
  rewrite <- Qmult_plus_distr_l.
  rewrite (Qabs_pos (1 # 2 * B * n)). 2: discriminate.
  rewrite <- (Qmult_comm (1 # 2 * B * n)), <- Qmult_assoc.
  apply (Qmult_le_l _ _ (Z.pos (2* B *n) # 1)).
  reflexivity. rewrite Qmult_assoc.
  setoid_replace ((Z.pos (2 * B * n) # 1) * (1 # 2 * B * n))%Q
    with 1%Q.
  rewrite Qmult_1_l.
  setoid_replace ((Z.pos (2 * B * n) # 1) * (2 # n))%Q
    with (Z.pos (2 * 2 * B) # 1)%Q.
  apply (Qle_trans _ (((Z.pos Az#1) + (Z.pos Ax#1)) *
                      Qabs (yn (2 * B * (2 * B * n))%positive))).
  apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
  apply Qplus_le_compat. rewrite HeqAz.
  apply Qlt_le_weak, (QCauchySeq_bounded_prop zn limz).
  rewrite HeqAx.
  apply Qlt_le_weak, (QCauchySeq_bounded_prop xn limx).
  rewrite Qmult_comm.
  apply (Qle_trans _ ((Z.pos Ay#1)* ((Z.pos Az # 1) + (Z.pos Ax # 1)))).
  apply Qmult_le_compat_r.
  rewrite HeqAy.
  apply Qlt_le_weak, (QCauchySeq_bounded_prop yn limy). discriminate.
  rewrite Qinv_plus_distr. subst B.
  unfold Qle, Qmult, Qplus, Qnum, Qden.
  repeat rewrite Pos.mul_1_r. repeat rewrite Z.mul_1_r.
  rewrite <- Pos2Z.inj_add, <- Pos2Z.inj_mul.
  apply Pos2Z.pos_le_pos. rewrite Pos.mul_add_distr_l.
  rewrite Pos.add_comm, Pos.mul_comm. apply belowMultiple.
  unfold Qeq, Qmult, Qnum, Qden.
  simpl. rewrite Pos.mul_1_r. rewrite Pos.mul_comm. reflexivity.
  unfold Qeq, Qmult, Qnum, Qden.
  simpl. rewrite Pos.mul_1_r, Pos.mul_1_r. reflexivity.
Qed.


Lemma CReal_mult_1_l : forall r: CReal, 1 * r == r.
Proof.
  intros [rn limr]. split.
  - intros [m maj]. simpl in maj.
    rewrite Qmult_1_l in maj.
    pose proof (QCauchySeq_bounded_prop (fun _ : positive => 1%Q) (ConstCauchy 1)).
    pose proof (QCauchySeq_bounded_prop rn limr).
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
    pose proof (QCauchySeq_bounded_prop (fun _ : positive => 1%Q) (ConstCauchy 1)).
    pose proof (QCauchySeq_bounded_prop rn limr).
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
Lemma CReal_mult_1_r : forall r, r * 1 == r.
Proof.
  intro; ring.
Qed.

Lemma CReal_opp_mult_distr_l
  : forall r1 r2 : CReal, - (r1 * r2) == (- r1) * r2.
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
    -> r * r1 == r * r2
    -> r1 == r2.
Proof.
  intros. destruct H; split.
  - intro abs. apply (CReal_mult_lt_compat_l (-r)) in abs.
    rewrite <- CReal_opp_mult_distr_l, <- CReal_opp_mult_distr_l, H0 in abs.
    exact (CRealLe_refl _ abs). apply (CReal_plus_lt_reg_l r).
    rewrite CReal_plus_opp_r, CReal_plus_comm, CReal_plus_0_l. exact c.
  - intro abs. apply (CReal_mult_lt_compat_l (-r)) in abs.
    rewrite <- CReal_opp_mult_distr_l, <- CReal_opp_mult_distr_l, H0 in abs.
    exact (CRealLe_refl _ abs). apply (CReal_plus_lt_reg_l r).
    rewrite CReal_plus_opp_r, CReal_plus_comm, CReal_plus_0_l. exact c.
  - intro abs. apply (CReal_mult_lt_compat_l r) in abs. rewrite H0 in abs.
    exact (CRealLe_refl _ abs). exact c.
  - intro abs. apply (CReal_mult_lt_compat_l r) in abs. rewrite H0 in abs.
    exact (CRealLe_refl _ abs). exact c.
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
    exists 4%positive. unfold inject_Q, CReal_minus, CReal_plus, proj1_sig.
    rewrite Qred_correct. simpl.
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

(* Find a positive index after which the Cauchy sequence proj1_sig x
   stays above 0, so that it can be inverted. *)
Lemma CRealPosShift_correct
  : forall (x : CReal) (xPos : 0 < x) (n : positive),
    Pos.le (proj1_sig xPos) n
    -> Qlt (1 # proj1_sig xPos) (proj1_sig x n).
Proof.
  intros x xPos p pmaj.
  destruct xPos as [n maj]; simpl in maj.
  apply (CRealLt_0_aboveSig x n).
  unfold proj1_sig in pmaj.
  apply (Qlt_le_trans _ _ _ maj).
  ring_simplify. apply Qle_refl. apply pmaj.
Qed.

Lemma CReal_inv_pos_cauchy
  : forall (x : CReal) (xPos : 0 < x) (k : positive),
    (forall n:positive, Pos.le k n -> Qlt (1 # k) (proj1_sig x n))
    -> QCauchySeq (fun n : positive => / proj1_sig x (k ^ 2 * n)%positive).
Proof.
  intros [xn xcau] xPos k maj. unfold proj1_sig.
  intros n p q H0 H1.
  setoid_replace (/ xn (k ^ 2 * p)%positive - / xn (k ^ 2 * q)%positive)%Q
    with ((xn (k ^ 2 * q)%positive -
           xn (k ^ 2 * p)%positive)
            / (xn (k ^ 2 * q)%positive *
               xn (k ^ 2 * p)%positive)).
  + apply (Qle_lt_trans _ (Qabs (xn (k ^ 2 * q)%positive
                                 - xn (k ^ 2 * p)%positive)
                                / (1 # (k^2)))).
    assert (1 # k ^ 2
            < Qabs (xn (k ^ 2 * q)%positive * xn (k ^ 2 * p)%positive))%Q.
    { rewrite Qabs_Qmult. unfold "^"%positive; simpl.
      rewrite factorDenom. rewrite Pos.mul_1_r.
      apply (Qlt_trans _ ((1#k) * Qabs (xn (k * k * p)%positive))).
      apply Qmult_lt_l. reflexivity. rewrite Qabs_pos.
      specialize (maj (k * k * p)%positive).
      apply maj. rewrite Pos.mul_comm, Pos.mul_assoc. apply belowMultiple.
      apply (Qle_trans _ (1 # k)).
      discriminate. apply Zlt_le_weak. apply maj.
      rewrite Pos.mul_comm, Pos.mul_assoc. apply belowMultiple.
      apply Qmult_lt_r. apply (Qlt_trans 0 (1#k)). reflexivity.
      rewrite Qabs_pos.
      specialize (maj (k * k * p)%positive).
      apply maj. rewrite Pos.mul_comm, Pos.mul_assoc. apply belowMultiple.
      apply (Qle_trans _ (1 # k)). discriminate.
      apply Zlt_le_weak. apply maj.
      rewrite Pos.mul_comm, Pos.mul_assoc. apply belowMultiple.
      rewrite Qabs_pos.
      specialize (maj (k * k * q)%positive).
      apply maj. rewrite Pos.mul_comm, Pos.mul_assoc. apply belowMultiple.
      apply (Qle_trans _ (1 # k)). discriminate.
      apply Zlt_le_weak.
      apply maj. rewrite Pos.mul_comm, Pos.mul_assoc. apply belowMultiple. }
    unfold Qdiv. rewrite Qabs_Qmult. rewrite Qabs_Qinv.
    rewrite Qmult_comm. rewrite <- (Qmult_comm (/ (1 # k ^ 2))).
    apply Qmult_le_compat_r. apply Qlt_le_weak.
    rewrite <- Qmult_1_l. apply Qlt_shift_div_r.
    apply (Qlt_trans 0 (1 # k ^ 2)). reflexivity. apply H.
    rewrite Qmult_comm. apply Qlt_shift_div_l.
    reflexivity. rewrite Qmult_1_l. apply H.
    apply Qabs_nonneg. simpl in maj.
    pose proof (xcau (n * (k^2))%positive
                     (k ^ 2 * q)%positive
                     (k ^ 2 * p)%positive).
    apply Qlt_shift_div_r. reflexivity.
    apply (Qlt_le_trans _ (1 # n * k ^ 2)). apply xcau.
    rewrite Pos.mul_comm. unfold id.
    apply Pos.mul_le_mono_l. exact H1.
    unfold id. rewrite Pos.mul_comm.
    apply Pos.mul_le_mono_l. exact H0.
    rewrite factorDenom. apply Qle_refl.
  + field. split. intro abs.
    specialize (maj (k ^ 2 * p)%positive).
    rewrite abs in maj. apply (Qlt_not_le (1#k) 0).
    apply maj. unfold "^"%positive; simpl. rewrite <- Pos.mul_assoc.
    rewrite Pos.mul_comm. apply belowMultiple. discriminate.
    intro abs.
    specialize (maj (k ^ 2 * q)%positive).
    rewrite abs in maj. apply (Qlt_not_le (1#k) 0).
    apply maj. unfold "^"%positive; simpl. rewrite <- Pos.mul_assoc.
    rewrite Pos.mul_comm. apply belowMultiple. discriminate.
Qed.

Definition CReal_inv_pos (x : CReal) (xPos : 0 < x) : CReal
  := exist _
           (fun n : positive => / proj1_sig x (proj1_sig xPos ^ 2 * n)%positive)
           (CReal_inv_pos_cauchy
              x xPos (proj1_sig xPos) (CRealPosShift_correct x xPos)).

Definition CReal_neg_lt_pos : forall x : CReal, x < 0 -> 0 < -x.
Proof.
  intros x [n nmaj]. exists n.
  apply (Qlt_le_trans _ _ _ nmaj). destruct x. simpl.
  unfold Qminus. rewrite Qplus_0_l, Qplus_0_r. apply Qle_refl.
Defined.

Definition CReal_inv (x : CReal) (xnz : x # 0) : CReal
  := match xnz with
     | inl xNeg => - CReal_inv_pos (-x) (CReal_neg_lt_pos x xNeg)
     | inr xPos => CReal_inv_pos x xPos
     end.

Notation "/ x" := (CReal_inv x) (at level 35, right associativity) : CReal_scope.

Lemma CReal_inv_0_lt_compat
  : forall (r : CReal) (rnz : r # 0),
    0 < r -> 0 < ((/ r) rnz).
Proof.
  intros. unfold CReal_inv. simpl.
  destruct rnz.
  - exfalso. apply CRealLt_asym in H. contradiction.
  - unfold CReal_inv_pos.
    pose proof (CRealPosShift_correct r c) as maj.
    destruct r as [xn cau].
    unfold CRealLt; simpl.
    destruct (Qarchimedean (xn 1%positive)) as [A majA].
    exists (2 * (A + 1))%positive. unfold Qminus. rewrite Qplus_0_r.
    rewrite <- (Qmult_1_l (/ xn (proj1_sig c ^ 2 * (2 * (A + 1)))%positive)).
    apply Qlt_shift_div_l. apply (Qlt_trans 0 (1# proj1_sig c)). reflexivity.
    apply maj. unfold "^"%positive, Pos.iter.
    rewrite <- Pos.mul_assoc, Pos.mul_comm. apply belowMultiple.
    rewrite <- (Qmult_inv_r (Z.pos A + 1 # 1)).
    setoid_replace (2 # 2 * (A + 1))%Q with (Qinv (Z.pos A + 1 # 1)).
    2: reflexivity.
    rewrite Qmult_comm. apply Qmult_lt_r. reflexivity.
    rewrite <- (Qplus_lt_l _ _ (- xn 1%positive)).
    apply (Qle_lt_trans _ (Qabs (xn (proj1_sig c ^ 2 * (2 * (A + 1)))%positive + - xn 1%positive))).
    apply Qle_Qabs. apply (Qlt_le_trans _ 1). apply cau.
    apply Pos.le_1_l. apply Pos.le_1_l.
    rewrite <- Qinv_plus_distr. rewrite <- (Qplus_comm 1).
    rewrite <- Qplus_0_r. rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
    rewrite Qplus_le_r. rewrite Qplus_0_l. apply Qlt_le_weak.
    apply Qlt_minus_iff in majA. apply majA.
    intro abs. inversion abs.
Defined.

Lemma CReal_linear_shift : forall (x : CReal) (k : positive),
    QCauchySeq (fun n => proj1_sig x (k * n)%positive).
Proof.
  intros [xn limx] k p n m H H0. unfold proj1_sig.
  apply limx. apply (Pos.le_trans _ n). apply H.
  rewrite <- (Pos.mul_1_l n). rewrite Pos.mul_assoc.
  apply Pos.mul_le_mono_r. destruct (k*1)%positive; discriminate.
  apply (Pos.le_trans _ (1*m)). exact H0.
  apply Pos.mul_le_mono_r. destruct k; discriminate.
Qed.

Lemma CReal_linear_shift_eq : forall (x : CReal) (k : positive),
    x ==
    (exist (fun n : positive -> Q => QCauchySeq n)
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

Lemma CReal_inv_l_pos : forall (r:CReal) (rnz : 0 < r),
    (CReal_inv_pos r rnz) * r == 1.
Proof.
  intros r c.
  unfold CReal_inv_pos.
  pose proof (CRealPosShift_correct r c) as maj.
  rewrite (CReal_mult_proper_l
             _ r (exist _ (fun n => proj1_sig r (proj1_sig c ^ 2 * n)%positive)
                        (CReal_linear_shift r _))).
  2: rewrite <- CReal_linear_shift_eq; apply reflexivity.
  apply CRealEq_diff. intro n.
  destruct r as [rn limr].
  unfold CReal_mult, inject_Q, proj1_sig.
  rewrite Qmult_comm, Qmult_inv_r.
  unfold Qminus. rewrite Qplus_opp_r, Qabs_pos.
  discriminate. apply Qle_refl.
  unfold proj1_sig in maj.
  intro abs.
  specialize (maj ((let (a, _) := c in a) ^ 2 *
            (2 *
             Pos.max
               (QCauchySeq_bound
                  (fun n : positive => Qinv (rn ((let (a, _) := c in a) ^ 2 * n))) id)
               (QCauchySeq_bound
                  (fun n : positive => rn ((let (a, _) := c in a) ^ 2 * n)) id) * n))%positive).
  simpl in maj. unfold proj1_sig in maj, abs.
  rewrite abs in maj. clear abs.
  apply (Qlt_not_le (1 # (let (a, _) := c in a)) 0).
  apply maj. unfold "^"%positive, Pos.iter.
  rewrite <- Pos.mul_assoc, Pos.mul_comm. apply belowMultiple.
  discriminate.
Qed.

Lemma CReal_inv_l : forall (r:CReal) (rnz : r # 0),
        ((/ r) rnz) * r == 1.
Proof.
  intros. unfold CReal_inv. destruct rnz.
  - rewrite <- CReal_opp_mult_distr_l, CReal_opp_mult_distr_r.
    apply CReal_inv_l_pos.
  - apply CReal_inv_l_pos.
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
      apply (Pos.le_trans _ (2*j)). apply belowMultiple.
      apply Pos.mul_le_mono_l.
      apply (Pos.le_trans _ (1 * Pos.max k (Pos.max i j))).
      rewrite Pos.mul_1_l.
      apply (Pos.le_trans _ (Pos.max i j) _ (Pos.le_max_r _ _)).
      apply Pos.le_max_r.
      rewrite <- Pos.mul_le_mono_r. destruct (Pos.max a b); discriminate.
      apply Qlt_le_weak. apply Qlt_minus_iff, (Qlt_trans _ (2#i)).
      reflexivity. apply imaj.
      apply (Pos.le_trans _ (2*i)). apply belowMultiple.
      apply Pos.mul_le_mono_l.
      apply (Pos.le_trans _ (1 * Pos.max k (Pos.max i j))).
      rewrite Pos.mul_1_l.
      apply (Pos.le_trans _ (Pos.max i j) _ (Pos.le_max_l _ _)).
      apply Pos.le_max_r.
      rewrite <- Pos.mul_le_mono_r. destruct (Pos.max a b); discriminate.
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
