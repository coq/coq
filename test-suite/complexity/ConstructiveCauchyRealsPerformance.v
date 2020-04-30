(* Here we give some functions that compute non-rational reals,
   to measure the computation speed. *)
(* Expected time < 5.00s *)

Require Import QArith Qabs.
Require Import ConstructiveCauchyRealsMult.

Local Open Scope CReal_scope.

Definition approx_sqrt_Q (q : Q) (n : positive) : Q
  := let (k,j) := q in
     match k with
     | Z0 => 0
     | Z.pos i => Z.pos (Pos.sqrt (i*j*n*n)) # (j*n)
     | Z.neg i => 0 (* unused *)
     end.

(* Approximation of the square root from below,
   improves the convergence modulus. *)
Lemma approx_sqrt_Q_le_below : forall (q : Q) (n : positive),
    Qle 0 q -> Qle (approx_sqrt_Q q n * approx_sqrt_Q q n) q.
Proof.
  intros. destruct q as [k j]. unfold approx_sqrt_Q.
  destruct k as [|i|i]. apply Z.le_refl.
  pose proof (Pos.sqrt_spec (i * j * n * n)). simpl in H0.
  destruct H0 as [H0 _].
  unfold Qle, Qmult, Qnum, Qden.
  rewrite <- Pos2Z.inj_mul, <- Pos2Z.inj_mul, <- Pos2Z.inj_mul.
  apply Pos2Z.pos_le_pos. rewrite (Pos.mul_comm i (j * n * (j * n))).
  rewrite <- (Pos.mul_comm j), <- (Pos.mul_assoc j), <- (Pos.mul_assoc j).
  apply Pos.mul_le_mono_l.
  apply (Pos.le_trans _ _ _ H0).
  rewrite <- (Pos.mul_comm n), <- (Pos.mul_assoc n).
  apply Pos.mul_le_mono_l.
  rewrite (Pos.mul_comm i j), <- Pos.mul_assoc, <- Pos.mul_assoc.
  apply Pos.mul_le_mono_l. rewrite Pos.mul_comm. apply Pos.le_refl.
  exfalso. unfold Qle, Z.le in H; simpl in H. exact (H eq_refl).
Qed.

Require Import Lia.

Lemma approx_sqrt_Q_le_below_lia : forall (q : Q) (n : positive),
    (0 <= q)%Q -> (approx_sqrt_Q q n * approx_sqrt_Q q n <= q)%Q.
Proof.
  intros. destruct q as [k j]. unfold approx_sqrt_Q.
  destruct k as [|i|i].
  - apply Z.le_refl.
  - unfold Qle, Qmult, Qnum, Qden.
    pose proof (Pos.sqrt_spec (i * j * n * n)) as Hsqrt; simpl in Hsqrt.
    destruct Hsqrt as [Hsqrt _]; apply (Pos.mul_le_mono_l j) in Hsqrt.
    lia.
  - unfold Qle, Qnum, Qden in H; lia.
Qed.

Print Assumptions approx_sqrt_Q_le_below_lia.

Lemma approx_sqrt_Q_lt_above : forall (q : Q) (n : positive),
    Qle 0 q -> Qlt q ((approx_sqrt_Q q n + (1#n)) * (approx_sqrt_Q q n + (1#n))).
Proof.
  intros. destruct q as [k j]. unfold approx_sqrt_Q.
  destruct k as [|i|i]. reflexivity.
  2: exfalso; unfold Qle, Z.le in H; simpl in H; exact (H eq_refl).
  pose proof (Pos.sqrt_spec (i * j * n * n)). simpl in H0.
  destruct H0 as [_ H0].
  apply (Qlt_le_trans
           _ (((Z.pos ((Pos.sqrt (i * j * n * n)) + 1) # j * n))
              * ((Z.pos ((Pos.sqrt (i * j * n * n)) + 1) # j * n)))).
  unfold Qlt, Qmult, Qnum, Qden.
  rewrite <- Pos2Z.inj_mul, <- Pos2Z.inj_mul, <- Pos2Z.inj_mul.
  apply Pos2Z.pos_lt_pos.
  rewrite Pos.mul_comm, <- Pos.mul_assoc, <- Pos.mul_assoc, Pos.mul_comm.
  apply Pos.mul_lt_mono_r. rewrite Pplus_one_succ_r in H0.
  refine (Pos.le_lt_trans _ _ _ _ H0). rewrite Pos.mul_comm.
  apply Pos.mul_le_mono_r.
  rewrite <- Pos.mul_assoc, (Pos.mul_comm i), <- Pos.mul_assoc.
  apply Pos.mul_le_mono_l. rewrite Pos.mul_comm. apply Pos.le_refl.
  setoid_replace (1#n)%Q with (Z.pos j#j*n)%Q. 2: reflexivity.
  rewrite Qinv_plus_distr.
  unfold Qle, Qmult, Qnum, Qden. apply Z.mul_le_mono_nonneg_r.
  discriminate. apply Z.mul_le_mono_nonneg.
  discriminate. 2: discriminate.
  rewrite Pos2Z.inj_add. apply Z.add_le_mono_l.
  apply Pos2Z.pos_le_pos. destruct j; discriminate.
  rewrite Pos2Z.inj_add. apply Z.add_le_mono_l.
  apply Pos2Z.pos_le_pos. destruct j; discriminate.
Qed.

Lemma approx_sqrt_Q_pos : forall (q : Q) (n : positive),
    Qle 0 q -> Qle 0 (approx_sqrt_Q q n).
Proof.
  intros. unfold approx_sqrt_Q. destruct q, Qnum.
  apply Qle_refl. discriminate. apply Qle_refl.
Qed.

Lemma Qsqrt_lt : forall q r :Q,
    (0 <= r -> q*q < r*r -> q < r)%Q.
Proof.
  intros. destruct (Q_dec q r). destruct s. exact q0.
  - exfalso. apply (Qlt_not_le _ _ H0). apply (Qle_trans _ (q * r)).
    apply Qmult_le_compat_r. apply Qlt_le_weak, q0. exact H.
    rewrite Qmult_comm.
    apply Qmult_le_compat_r. apply Qlt_le_weak, q0.
    apply (Qle_trans _ r _ H). apply Qlt_le_weak, q0.
  - exfalso. rewrite q0 in H0. exact (Qlt_irrefl _ H0).
Qed.

Lemma approx_sqrt_Q_cauchy :
  forall q:Q, QCauchySeq (approx_sqrt_Q q).
Proof.
  intro q. destruct q as [k j]. destruct k.
  - intros n a b H H0. reflexivity.
  - assert (forall n a b, Pos.le n b ->
               (approx_sqrt_Q (Z.pos p # j) a - approx_sqrt_Q (Z.pos p # j) b
                < 1 # n)%Q).
    { intros. rewrite <- (Qplus_lt_r _ _ (approx_sqrt_Q (Z.pos p # j) b)).
      ring_simplify. apply Qsqrt_lt.
      apply (Qle_trans _ (0+(1#n))). rewrite Qplus_0_l. discriminate.
      apply Qplus_le_l. apply approx_sqrt_Q_pos. discriminate.
      apply (Qle_lt_trans _ (Z.pos p # j)).
      apply approx_sqrt_Q_le_below. discriminate.
      apply (Qlt_le_trans _ ((approx_sqrt_Q (Z.pos p # j) b + (1 # b)) *
                             (approx_sqrt_Q (Z.pos p # j) b + (1 # b)))).
      apply approx_sqrt_Q_lt_above. discriminate.
      apply (Qle_trans _ ((approx_sqrt_Q (Z.pos p # j) b + (1 # n)) *
                          (approx_sqrt_Q (Z.pos p # j) b + (1 # b)))).
      apply Qmult_le_r.
      apply (Qlt_le_trans _ (0+(1#b))). rewrite Qplus_0_l. reflexivity.
      apply Qplus_le_l. apply approx_sqrt_Q_pos. discriminate.
      apply Qplus_le_r. unfold Qle; simpl.
      apply Pos2Z.pos_le_pos, H.
      apply Qmult_le_l.
      apply (Qlt_le_trans _ (0+(1#n))). rewrite Qplus_0_l. reflexivity.
      apply Qplus_le_l. apply approx_sqrt_Q_pos. discriminate.
      apply Qplus_le_r. unfold Qle; simpl.
      apply Pos2Z.pos_le_pos, H. }
    intros n a b H0 H1. apply Qabs_case.
    intros. apply H, H1.
    intros.
    setoid_replace (- (approx_sqrt_Q (Z.pos p # j) a - approx_sqrt_Q (Z.pos p # j) b))%Q
      with (approx_sqrt_Q (Z.pos p # j) b - approx_sqrt_Q (Z.pos p # j) a)%Q.
    2: ring. apply H, H0.
  - intros n a b H H0. reflexivity.
Qed.

Definition CReal_sqrt_Q (q : Q) : CReal
  := exist _ (approx_sqrt_Q q) (approx_sqrt_Q_cauchy q).


Time Eval vm_compute in (proj1_sig (CReal_sqrt_Q 2) (10 ^ 400)%positive).
