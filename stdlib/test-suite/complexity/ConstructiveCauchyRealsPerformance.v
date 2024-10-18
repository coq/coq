(* Here we give some functions that compute non-rational reals,
   to measure the computation speed. *)
(* Expected time < 5.00s *)

From Stdlib Require Import QArith Qabs Qpower.
From Stdlib Require Import ConstructiveCauchyRealsMult.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.

Local Open Scope CReal_scope.

(* We would need a shift instruction on positives to do this properly *)

Definition CReal_sqrt_Q_seq (q : Q) (n : Z) : Q
  := let (k,j) := q in
     match k with
     | Z0 => 0
     | Z.pos i => match n with
         | Z0
         | Z.pos _ => Z.pos (Pos.sqrt (i*j)) # (j)
         | Z.neg n' => Z.pos (Pos.sqrt (i*j*2^(2*n'))) # (j*2^n')
         end
     | Z.neg i => 0 (* unused *)
     end.

Local Lemma Pos_pow_twice_r a b : (a^(2*b) = a^b * a^b)%positive.
Proof.
  apply Pos2Z.inj.
  rewrite Pos2Z.inj_mul.
  do 2 rewrite Pos2Z.inj_pow.
  rewrite Pos2Z.inj_mul.
  apply Z.pow_twice_r.
Qed.

(* Approximation of the square root from below,
   improves the convergence modulus. *)
Lemma CReal_sqrt_Q_le_below : forall (q : Q) (n : Z),
    (0<=q)%Q -> (CReal_sqrt_Q_seq q n * CReal_sqrt_Q_seq q n <= q)%Q.
Proof.
  intros q n Hqpos. destruct q as [k j]. unfold CReal_sqrt_Q_seq.
  destruct k as [|i|i].
  - apply Z.le_refl.
  - destruct n as [|n|n].
    + pose proof (Pos.sqrt_spec (i * j)) as H. simpl in H.
      destruct H as [H _].
      unfold Qle, Qmult, Qnum, Qden.
      rewrite <- Pos2Z.inj_mul, <- Pos2Z.inj_mul, <- Pos2Z.inj_mul.
      apply Pos2Z.pos_le_pos. rewrite (Pos.mul_assoc i j j).
      apply Pos.mul_le_mono_r; exact H.
    + pose proof (Pos.sqrt_spec (i * j)) as H. simpl in H.
      destruct H as [H _].
      unfold Qle, Qmult, Qnum, Qden.
      rewrite <- Pos2Z.inj_mul, <- Pos2Z.inj_mul, <- Pos2Z.inj_mul.
      apply Pos2Z.pos_le_pos. rewrite (Pos.mul_assoc i j j).
      apply Pos.mul_le_mono_r; exact H.
    + pose proof (Pos.sqrt_spec (i * j * 2^(2*n))) as H. simpl in H.
      destruct H as [H _].
      unfold Qle, Qmult, Qnum, Qden.
      rewrite <- Pos2Z.inj_mul, <- Pos2Z.inj_mul, <- Pos2Z.inj_mul.
      apply Pos2Z.pos_le_pos. rewrite (Pos.mul_comm j (2^n)) at 2.
      do 3 rewrite Pos.mul_assoc.
      apply Pos.mul_le_mono_r.
      simpl.
      rewrite Pos_pow_twice_r in H at 3.
      rewrite Pos.mul_assoc in H.
      exact H.
  - exact Hqpos.
Qed.

Lemma CReal_sqrt_Q_lt_above : forall (q : Q) (n : Z),
    (0 <= q)%Q -> (q < ((CReal_sqrt_Q_seq q n + 2^n) * (CReal_sqrt_Q_seq q n + 2^n)))%Q.
Proof.
  intros. destruct q as [k j]. unfold CReal_sqrt_Q_seq.
  destruct k as [|i|i].
  - ring_simplify.
    setoid_rewrite <- Qpower_mult.
    setoid_rewrite Qreduce_zero.
    pose proof Qpower_0_lt 2 (n*2)%Z ltac:(lra).
    lra.
  - destruct n as [|n|n].
    + pose proof (Pos.sqrt_spec (i * j)). simpl in H0.
      destruct H0 as [_ H0].
      change (2^0)%Q with 1%Q.
      unfold Qlt, Qplus, Qmult, Qnum, Qden.
      rewrite Pos.mul_1_r, Z.mul_1_r, Z.mul_1_l.
      repeat rewrite <- Pos2Z.inj_add, <- Pos2Z.inj_mul.
      apply Pos2Z.pos_lt_pos.
      rewrite Pos.mul_assoc.
      apply Pos.mul_lt_mono_r.
      apply (Pos.lt_le_trans _ _ _ H0).
      apply Pos.mul_le_mono; lia.
    + pose proof (Pos.sqrt_spec (i * j)). simpl in H0.
      destruct H0 as [_ H0].
      rewrite Qpower_decomp_pos.
      unfold Qlt, Qplus, Qmult, Qnum, Qden.
      rewrite PosExtra.Pos_pow_1_r.
      rewrite Pos.mul_1_r, Z.mul_1_r.
      rewrite <- Pos2Z.inj_pow; do 2 rewrite <- Pos2Z.inj_mul; rewrite <- Pos2Z.inj_add.
      apply Pos2Z.pos_lt_pos.
      rewrite Pos.mul_assoc.
      apply Pos.mul_lt_mono_r.
      apply (Pos.lt_le_trans _ _ _ H0).
      apply Pos.mul_le_mono;
        pose proof Pos.le_1_l (2 ^ n * j)%positive; lia.
    + pose proof (Pos.sqrt_spec (i * j * 2 ^ (2 * n))). simpl in H0.
      destruct H0 as [_ H0].
      rewrite <- Pos2Z.opp_pos, Qpower_opp.
      rewrite Qpower_decomp_pos.
      rewrite <- Pos2Z.inj_pow, PosExtra.Pos_pow_1_r, Qinv_pos.
      unfold Qlt, Qplus, Qmult, Qnum, Qden.
      repeat rewrite  Pos2Z.inj_mul.
      ring_simplify.
      replace (Z.pos i * Z.pos j ^ 2 * Z.pos (2 ^ n) ^ 4)%Z
      with ((Z.pos i * Z.pos j * Z.pos (2 ^ n) ^ 2) * (Z.pos j * Z.pos (2 ^ n) ^ 2))%Z by ring.
      replace (
        Z.pos j ^ 3 * Z.pos (2 ^ n) ^ 2 +
        2 * Z.pos j ^ 2 * Z.pos (2 ^ n) ^ 2 * Z.pos (Pos.sqrt (i * j * 2 ^ (2 * n))) +
        Z.pos j * Z.pos (2 ^ n) ^ 2 * Z.pos (Pos.sqrt (i * j * 2 ^ (2 * n))) ^ 2)%Z
      with (
        (Z.pos j + Z.pos (Pos.sqrt (i * j * 2 ^ (2 * n))))^2 *
        (Z.pos j * Z.pos (2 ^ n) ^ 2))%Z by ring.
      repeat rewrite Pos2Z.inj_pow.
      rewrite <- Z.pow_mul_r by lia.
      repeat rewrite <- Pos2Z.inj_mul.
      repeat rewrite <- Pos2Z.inj_pow.
      repeat rewrite <- Pos2Z.inj_mul.
      repeat rewrite <- Pos2Z.inj_add.
      apply Pos2Z.pos_lt_pos.
      rewrite (Pos.mul_comm n 2); change (2*n)%positive with (n~0)%positive.
      apply Pos.mul_lt_mono_r.
      apply (Pos.lt_le_trans _ _ _ H0).
      apply Pos.mul_le_mono;
        pose proof Pos.le_1_l (2 ^ n * j)%positive; lia.
 - exfalso; unfold Qle, Z.le in H; simpl in H; exact (H eq_refl).
Qed.

Lemma CReal_sqrt_Q_pos : forall (q : Q) (n : Z),
   (0 <= (CReal_sqrt_Q_seq q n))%Q.
Proof.
  intros. unfold CReal_sqrt_Q_seq. destruct q, Qnum.
  - apply Qle_refl.
  - destruct n as [|n|n]; discriminate.
  - apply Qle_refl.
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

Lemma CReal_sqrt_Q_cauchy :
  forall q:Q, QCauchySeq (CReal_sqrt_Q_seq q).
Proof.
  intro q. destruct q as [k j]. destruct k.
  - intros n a b H H0.
    change (Qabs _) with 0%Q.
    apply Qpower_0_lt; reflexivity.
  - assert (forall n a b, (b<=n)%Z ->
               (CReal_sqrt_Q_seq (Z.pos p # j) a - CReal_sqrt_Q_seq (Z.pos p # j) b
                < 2^n)%Q).
    { intros.
      pose proof Qpower_0_lt 2 n eq_refl as Hpow.
      rewrite <- (Qplus_lt_r _ _ (CReal_sqrt_Q_seq (Z.pos p # j) b)).
      ring_simplify. apply Qsqrt_lt.
        { apply (Qle_trans _ (0+2^n)). lra.
          apply Qplus_le_l. apply CReal_sqrt_Q_pos. }
      apply (Qle_lt_trans _ (Z.pos p # j)).
        { apply CReal_sqrt_Q_le_below. discriminate. }
      apply (Qlt_le_trans _ ((CReal_sqrt_Q_seq (Z.pos p # j) b + (2^b)) *
                             (CReal_sqrt_Q_seq (Z.pos p # j) b + (2^b)))).
        { apply CReal_sqrt_Q_lt_above. discriminate. }
      apply (Qle_trans _ ((CReal_sqrt_Q_seq (Z.pos p # j) b + (2^n)) *
                          (CReal_sqrt_Q_seq (Z.pos p # j) b + (2^b)))).
        { apply Qmult_le_r.
          - apply (Qlt_le_trans _ (0+(2^b))).
            + rewrite Qplus_0_l. apply Qpower_0_lt. reflexivity.
            + apply Qplus_le_l. apply CReal_sqrt_Q_pos.
          - apply Qplus_le_r. apply Qpower_le_compat_l.
              exact H. discriminate. }
      apply Qmult_le_compat_nonneg.
      - split.
        + pose proof CReal_sqrt_Q_pos (Z.pos p # j) b.
          lra.
        + apply Qle_refl.
      - split.
        + pose proof CReal_sqrt_Q_pos (Z.pos p # j) b.
          pose proof Qpower_0_lt 2 b eq_refl as Hpowb.
          lra.
        + apply Qplus_le_r.
          apply Qpower_le_compat_l.
            exact H. discriminate.
    }
    intros n a b H0 H1. apply Qabs_case.
    intros. apply H, H1.
    intros.
    setoid_replace (- (CReal_sqrt_Q_seq (Z.pos p # j) a - CReal_sqrt_Q_seq (Z.pos p # j) b))%Q
      with (CReal_sqrt_Q_seq (Z.pos p # j) b - CReal_sqrt_Q_seq (Z.pos p # j) a)%Q.
    2: ring. apply H, H0.
  - intros n a b H H0.
    change (Qabs _) with 0%Q.
    apply Qpower_0_lt; reflexivity.
Qed.

Definition CReal_sqrt_Q_scale (q : Q) : Z
  := ((QExtra.Qbound_lt_ZExp2 q + 1)/2)%Z.

Lemma CReal_sqrt_Q_bound : forall (q : Q),
  QBound (CReal_sqrt_Q_seq q) (CReal_sqrt_Q_scale q).
Proof.
  intros q k.
  unfold CReal_sqrt_Q_scale.
  rewrite Qabs_pos.
    2: apply CReal_sqrt_Q_pos.
  apply Qsqrt_lt.
    1: apply Qpower_pos; discriminate.
  destruct (Qlt_le_dec q 0) as [Hq|Hq].
  - destruct q as [[|n|n] d].
    + discriminate Hq.
    + discriminate Hq.
    + reflexivity.
  - apply (Qle_lt_trans _ _ _ (CReal_sqrt_Q_le_below _ _ Hq)).
    rewrite <- Qpower_plus.
      2: discriminate.
    rewrite Z.add_diag, Z.mul_comm.
    pose proof Zdiv.Zmod_eq (QExtra.Qbound_lt_ZExp2 q + 1) 2 eq_refl as Hmod.
    assert (forall a b c : Z, c=b-a -> a=b-c)%Z as H by (intros a b c H'; rewrite H';  ring).
    apply H in Hmod; rewrite Hmod; clear H Hmod.
    apply (Qlt_le_trans _ _ _ (QExtra.Qbound_lt_ZExp2_spec q)).
    apply Qpower_le_compat_l. 2: discriminate.
    pose proof Z.mod_pos_bound (QExtra.Qbound_lt_ZExp2 q + 1)%Z 2%Z eq_refl.
    lia.
Qed.

Definition CReal_sqrt_Q (q : Q) : CReal :=
{|
  seq := CReal_sqrt_Q_seq q;
  scale := CReal_sqrt_Q_scale q;
  cauchy := CReal_sqrt_Q_cauchy q;
  bound := CReal_sqrt_Q_bound q
|}.

Time Eval vm_compute in (seq (CReal_sqrt_Q 2) (-1000)%Z).
