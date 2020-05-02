Require Import PArith.
Require Import ZArith.
Require Import Lia.

Lemma Pos_pow_1_r: forall p : positive,
  (1^p = 1)%positive.
Proof.
  intros p.
  assert (forall q:positive, Pos.iter id 1 q = 1)%positive as H1.
  { intros q; apply Pos.iter_invariant; tauto. }
  induction p.
  - cbn; rewrite IHp, H1; reflexivity.
  - cbn; rewrite IHp, H1; reflexivity.
  - reflexivity.
Qed.

Lemma Pos_le_multiple : forall n p : positive, (n <= p * n)%positive.
Proof.
  intros n p.
  rewrite <- (Pos.mul_1_l n) at 1.
  apply Pos.mul_le_mono_r.
  destruct p; discriminate.
Qed.

Lemma Pos_pow_le_mono_r : forall a b c : positive,
    (b <= c)%positive
 -> (a ^ b <= a ^ c)%positive.
Proof.
  intros a b c.
  pose proof Z.pow_le_mono_r (Z.pos a) (Z.pos b) (Z.pos c).
  lia.
Qed.
