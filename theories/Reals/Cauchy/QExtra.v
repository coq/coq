Require Import QArith.
Require Import Qpower.
Require Import Qabs.
Require Import Qround.
Require Import Lia.
Require Import Lqa. (* This is only used in a few places and could be avoided *)
Require Import PosExtra.

(** * Lemmas on Q numerator denominator operations *)

Lemma Q_factorDenom : forall (a:Z) (b d:positive), (a # (d * b)) == (1#d) * (a#b).
Proof.
  intros. unfold Qeq. simpl. destruct a; reflexivity.
Qed.

Lemma Q_factorNum_l : forall (a b : Z) (c : positive),
  (a*b # c == (a # 1) * (b # c))%Q.
Proof.
  intros a b c.
  unfold Qeq; cbn; lia.
Qed.

Lemma Q_factorNum : forall (a : Z) (b : positive),
  (a # b == (a # 1) * (1 # b))%Q.
Proof.
  intros a b.
  unfold Qeq; cbn; lia.
Qed.

Lemma Q_reduce_fl : forall (a b : positive),
  (Z.pos a # a * b == (1 # b))%Q.
Proof.
  intros a b.
  unfold Qeq; cbn; lia.
Qed.

(** * Lemmas on Q comparison *)

Lemma Qle_neq: forall p q : Q, p < q <-> p <= q /\ ~ (p == q).
Proof.
  intros p q; split; intros H.
  - rewrite Qlt_alt in H; rewrite Qle_alt, Qeq_alt.
    rewrite H; split; intros H1; inversion H1.
  - rewrite Qlt_alt; rewrite Qle_alt, Qeq_alt in H.
    destruct (p ?= q); tauto.
Qed.

Lemma Qplus_lt_compat : forall x y z t : Q,
  (x < y)%Q -> (z < t)%Q -> (x + z < y + t)%Q.
Proof.
  intros x y z t H1 H2.
  apply Qplus_lt_le_compat.
  - assumption.
  - apply Qle_lteq; left; assumption.
Qed.

(* Qgt is just a notation, but one might now know this and search for this lemma *)

Lemma Qgt_lt: forall p q : Q, p > q -> q < p.
Proof.
  intros p q H; assumption.
Qed.

Lemma Qlt_gt: forall p q : Q, p < q -> q > p.
Proof.
  intros p q H; assumption.
Qed.

Notation "x <= y < z" := (x<=y/\y<z) : Q_scope.
Notation "x < y <= z" := (x<y/\y<=z) : Q_scope.
Notation "x < y < z" := (x<y/\y<z) : Q_scope.

(** * Lemmas on Qmult *)

Lemma Qmult_lt_0_compat : forall a b : Q,
    0 < a
 -> 0 < b
 -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  destruct a,b. unfold Qlt, Qmult, QArith_base.Qnum, QArith_base.Qden in *.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_0_l, Z.mul_1_r in *.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma Qmult_lt_1_compat:
  forall a b : Q, (1 < a)%Q -> (1 < b)%Q -> (1 < a * b)%Q.
Proof.
  intros a b Ha Hb.
  pose proof Qmult_lt_0_compat (a-1) (b-1) ltac:(lra) ltac:(lra).
  lra.
Qed.

Lemma Qmult_le_1_compat:
  forall a b : Q, (1 <= a)%Q -> (1 <= b)%Q -> (1 <= a * b)%Q.
Proof.
  intros a b Ha Hb.
  pose proof Qmult_le_0_compat (a-1) (b-1) ltac:(lra) ltac:(lra).
  lra.
Qed.

Lemma Qmult_lt_compat_nonneg: forall x y z t : Q,
  (0 <= x < y)%Q -> (0 <= z < t)%Q -> (x * z < y * t)%Q.
Proof.
  intros [xn xd] [yn yd] [zn zd] [tn td] [H0lex Hxlty] [H0lez Hzltt].
  (* ToDo: why do I need path qualification to Qnum? It is exported by QArith *)
  unfold Qmult, Qlt, Qle, QArith_base.Qnum, QArith_base.Qden in *.
  do 2 rewrite Pos2Z.inj_mul.
  setoid_replace (xn * zn * (Z.pos yd * Z.pos td))%Z with ((xn * Z.pos yd) * (zn * Z.pos td))%Z by ring.
  setoid_replace (yn * tn * (Z.pos xd * Z.pos zd))%Z with ((yn * Z.pos xd) * (tn * Z.pos zd))%Z by ring.
  apply Z.mul_lt_mono_nonneg.
  - rewrite <- (Z.mul_0_l 0); apply Z.mul_le_mono_nonneg; lia.
  - exact Hxlty.
  - rewrite <- (Z.mul_0_l 0); apply Z.mul_le_mono_nonneg; lia.
  - exact Hzltt.
Qed.

Lemma Qmult_lt_le_compat_nonneg: forall x y z t : Q,
  (0 < x <= y)%Q -> (0 < z < t)%Q -> (x * z < y * t)%Q.
Proof.
  intros [xn xd] [yn yd] [zn zd] [tn td] [H0lex Hxlty] [H0lez Hzltt].
  (* ToDo: why do I need path qualification to Qnum? It is exported by QArith *)
  unfold Qmult, Qlt, Qle, QArith_base.Qnum, QArith_base.Qden in *.
  do 2 rewrite Pos2Z.inj_mul.
  setoid_replace (xn * zn * (Z.pos yd * Z.pos td))%Z with ((xn * Z.pos yd) * (zn * Z.pos td))%Z by ring.
  setoid_replace (yn * tn * (Z.pos xd * Z.pos zd))%Z with ((yn * Z.pos xd) * (tn * Z.pos zd))%Z by ring.
  apply Zmult_lt_compat2; split.
  - rewrite <- (Z.mul_0_l 0). apply Z.mul_lt_mono_nonneg; lia.
  - exact Hxlty.
  - rewrite <- (Z.mul_0_l 0). apply Z.mul_lt_mono_nonneg; lia.
  - exact Hzltt.
Qed.

Lemma Qmult_le_compat_nonneg: forall x y z t : Q,
  (0 <= x <= y)%Q -> (0 <= z <= t)%Q -> (x * z <= y * t)%Q.
Proof.
  intros [xn xd] [yn yd] [zn zd] [tn td] [H0lex Hxlty] [H0lez Hzltt].
  (* ToDo: why do I need path qualification to Qnum? It is exported by QArith *)
  unfold Qmult, Qlt, Qle, QArith_base.Qnum, QArith_base.Qden in *.
  do 2 rewrite Pos2Z.inj_mul.
  setoid_replace (xn * zn * (Z.pos yd * Z.pos td))%Z with ((xn * Z.pos yd) * (zn * Z.pos td))%Z by ring.
  setoid_replace (yn * tn * (Z.pos xd * Z.pos zd))%Z with ((yn * Z.pos xd) * (tn * Z.pos zd))%Z by ring.
  apply Z.mul_le_mono_nonneg.
  - rewrite <- (Z.mul_0_l 0); apply Z.mul_le_mono_nonneg; lia.
  - exact Hxlty.
  - rewrite <- (Z.mul_0_l 0); apply Z.mul_le_mono_nonneg; lia.
  - exact Hzltt.
Qed.

(** * Lemmas on Qinv *)

Lemma Qinv_swap_pos: forall (a b : positive),
  Z.pos a # b == / (Z.pos b # a).
Proof.
  intros a b.
  reflexivity.
Qed.

Lemma Qinv_swap_neg: forall (a b : positive),
  Z.neg a # b == / (Z.neg b # a).
Proof.
  intros a b.
  reflexivity.
Qed.

(** * Lemmas on Qabs *)

Lemma Qabs_Qlt_condition: forall x y : Q,
  Qabs x < y <-> -y < x < y.
Proof.
 split.
  split.
   rewrite <- (Qopp_opp x).
   apply Qopp_lt_compat.
   apply Qle_lt_trans with (Qabs (-x)).
   apply Qle_Qabs.
   now rewrite Qabs_opp.
  apply Qle_lt_trans with (Qabs x); auto using Qle_Qabs.
 intros (H,H').
 apply Qabs_case; trivial.
 intros. rewrite <- (Qopp_opp y). now apply Qopp_lt_compat.
Qed.

Lemma Qabs_gt: forall r s : Q,
    (r < s)%Q -> (r < Qabs s)%Q.
Proof.
  intros r s Hrlts.
  apply Qabs_case; intros; lra.
Qed.

(** * Lemmas on Qpower *)

Lemma Qpower_0_r: forall q:Q,
  q^0 == 1.
Proof.
  intros q.
  reflexivity.
Qed.

Lemma Qpower_1_r: forall q:Q,
  q^1 == q.
Proof.
  intros q.
  reflexivity.
Qed.

Lemma Qpower_not_0: forall (a : Q) (z : Z),
  ~ a == 0 -> ~ Qpower a z == 0.
Proof.
  intros a z H; destruct z.
  - discriminate.
  - apply Qpower_not_0_positive; assumption.
  - cbn. intros H1.
    pose proof Qmult_inv_r (Qpower_positive a p) as H2.
    specialize (H2 (Qpower_not_0_positive _ _ H)).
    rewrite H1, Qmult_0_r in H2.
    discriminate H2.
Qed.

(* Actually Qpower_pos should be named Qpower_nonneg *)

Lemma Qpower_pos_lt: forall (a : Q) (z : Z),
  a > 0 -> Qpower a z > 0.
Proof.
  intros q z Hpos.
  pose proof Qpower_pos q z (Qlt_le_weak 0 q Hpos) as H1.
  pose proof Qpower_not_0 q z as H2.
  pose proof Qlt_not_eq 0 q Hpos as H3.
  specialize (H2 (Qnot_eq_sym _ _ H3)); clear H3.
  apply Qnot_eq_sym in H2.
  apply Qle_neq; split; assumption.
Qed.

Lemma Qpower_minus: forall (a : Q) (n m : Z),
  ~ a == 0 -> a ^ (n - m) == a ^ n / a ^ m.
Proof.
  intros a n m Hnz.
  rewrite <- Z.add_opp_r.
  rewrite Qpower_plus by assumption.
  rewrite Qpower_opp.
  field.
  apply Qpower_not_0; assumption.
Qed.

Lemma Qpower_minus_pos: forall (a b : positive) (n m : Z),
  (Z.pos a#b) ^ (n - m) == (Z.pos a#b) ^ n * (Z.pos b#a) ^ m.
Proof.
  intros a b n m.
  rewrite Qpower_minus by discriminate.
  rewrite (Qinv_swap_pos b a), Qinv_power.
  reflexivity.
Qed.

Lemma Qpower_minus_neg: forall (a b : positive) (n m : Z),
  (Z.neg a#b) ^ (n - m) == (Z.neg a#b) ^ n * (Z.neg b#a) ^ m.
Proof.
  intros a b n m.
  rewrite Qpower_minus by discriminate.
  rewrite (Qinv_swap_neg b a), Qinv_power.
  reflexivity.
Qed.

Lemma Qpower_lt_1_increasing:
  forall (q : Q) (n : positive), (1<q)%Q -> (1 < q ^ (Z.pos n))%Q.
Proof.
  intros q n Hq.
  induction n.
  - cbn in *.
    apply Qmult_lt_1_compat. assumption.
    apply Qmult_lt_1_compat; assumption.
  - cbn in *.
    apply Qmult_lt_1_compat; assumption.
  - cbn; assumption.
Qed.

Lemma Qpower_lt_1_increasing':
  forall (q : Q) (n : Z), (1<q)%Q -> (0<n)%Z -> (1 < q ^ n)%Q.
Proof.
  intros q n Hq Hn.
  destruct n.
  - inversion Hn.
  - apply Qpower_lt_1_increasing; assumption.
  - lia.
Qed.

Lemma Qzero_eq: forall (d : positive),
  (0#d == 0)%Q.
Proof.
  intros d.
  unfold Qeq, Qnum, Qden; reflexivity.
Qed.

Lemma Qpower_le_1_increasing:
  forall (q : Q) (n : positive), (1<=q)%Q -> (1 <= q ^ (Z.pos n))%Q.
Proof.
  intros q n Hq.
  induction n.
  - cbn in *.
    apply Qmult_le_1_compat. assumption.
    apply Qmult_le_1_compat; assumption.
  - cbn in *.
    apply Qmult_le_1_compat; assumption.
  - cbn; assumption.
Qed.

Lemma Qpower_le_1_increasing':
  forall (q : Q) (n : Z), (1<=q)%Q -> (0<=n)%Z -> (1 <= q ^ n)%Q.
Proof.
  intros q n Hq Hn.
  destruct n.
  - apply Qle_refl.
  - apply Qpower_le_1_increasing; assumption.
  - lia.
Qed.

(* ToDo: check if name compat_r is more appropriate *)

Lemma Qpower_lt_compat:
  forall (q : Q) (n m : Z), (n < m)%Z -> (1<q)%Q -> (q ^ n < q ^ m)%Q.
Proof.
  intros q n m Hnm Hq.
  replace m with (n+(m-n))%Z by ring.
  rewrite Qpower_plus, <- Qmult_1_r, <- Qmult_assoc.
    2: lra.
  rewrite Qmult_lt_l, Qmult_1_l.
    2: apply Qpower_pos_lt; lra.
  remember (m-n)%Z as k.
  apply Qpower_lt_1_increasing'.
  - exact Hq.
  - lia.
Qed.

Lemma Qpower_le_compat:
  forall (q : Q) (n m : Z), (n <= m)%Z -> (1<=q)%Q -> (q ^ n <= q ^ m)%Q.
Proof.
  intros q n m Hnm Hq.
  replace m with (n+(m-n))%Z by ring.
  rewrite Qpower_plus, <- Qmult_1_r, <- Qmult_assoc.
    2: lra.
  rewrite Qmult_le_l, Qmult_1_l.
    2: apply Qpower_pos_lt; lra.
  remember (m-n)%Z as k.
  apply Qpower_le_1_increasing'.
  - exact Hq.
  - lia.
Qed.

Lemma Qpower_lt_compat_inv:
  forall (q : Q) (n m : Z), (q ^ n < q ^ m)%Q -> (1<q)%Q -> (n < m)%Z.
Proof.
  intros q n m Hnm Hq.
  destruct (Z_lt_le_dec n m) as [Hd|Hd].
  - assumption.
  - pose proof Qpower_le_compat q m n Hd ltac:(lra).
  lra.
Qed.

Lemma Qpower_le_compat_inv:
  forall (q : Q) (n m : Z), (q ^ n <= q ^ m)%Q -> (1<q)%Q -> (n <= m)%Z.
Proof.
  intros q n m Hnm Hq.
  destruct (Z_lt_le_dec m n) as [Hd|Hd].
  - pose proof Qpower_lt_compat q m n Hd Hq.
    lra.
  - assumption.
Qed.

Lemma Qpower_decomp': forall (p : positive) (a : Z) (b : positive),
  (a # b) ^ (Z.pos p) == a ^ (Z.pos p) # (b ^ p)%positive.
Proof.
  intros p a b.
  pose proof Qpower_decomp p a b.
  cbn; rewrite H; reflexivity.
Qed.


(** * Power of 2 open and closed upper and lower bounds for [q : Q] *)

Lemma QarchimedeanExp2_Pos : forall q : Q,
  {p : positive | (q < Z.pos (2^p) # 1)%Q}.
Proof.
  intros q.
  destruct (Qarchimedean q) as [pexp Hpexp].
  exists (Pos.size pexp).
  pose proof Pos.size_gt pexp as H1.
  unfold Qlt in *. cbn in *; Zify.zify.
  apply (Z.mul_lt_mono_pos_r (QDen q)) in H1; [|assumption].
  apply (Z.lt_trans _ _ _ Hpexp H1).
Qed.

Fixpoint Pos_log2floor_plus1 (p : positive) : positive :=
  match p with
  | (p'~1)%positive => Pos.succ (Pos_log2floor_plus1 p')
  | (p'~0)%positive => Pos.succ (Pos_log2floor_plus1 p')
  | 1%positive      => 1
  end.

Lemma Pos_log2floor_plus1_spec : forall (p : positive),
  (Pos.pow 2 (Pos_log2floor_plus1 p) <= 2 * p < 2 * Pos.pow 2 (Pos_log2floor_plus1 p))%positive.
Proof.
  intros p.
  split.
  - induction p.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. lia.
  - induction p.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. lia.
Qed.

Fixpoint Pos_log2ceil_plus1 (p : positive) : positive :=
  match p with
  | (p'~1)%positive => Pos.succ (Pos.succ (Pos_log2floor_plus1 p'))
  | (p'~0)%positive => Pos.succ (Pos_log2ceil_plus1 p')
  | 1%positive      => 1
  end.

Lemma Pos_log2ceil_plus1_spec : forall (p : positive),
  (Pos.pow 2 (Pos_log2ceil_plus1 p) < 4 * p <= 2 * Pos.pow 2 (Pos_log2ceil_plus1 p))%positive.
Proof.
  intros p.
  split.
  - induction p.
    + cbn. do 2 rewrite Pos.pow_succ_r.
      pose proof Pos_log2floor_plus1_spec p. lia.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. lia.
  - induction p.
    + cbn. do 2 rewrite Pos.pow_succ_r.
      pose proof Pos_log2floor_plus1_spec p. lia.
    + cbn. rewrite Pos.pow_succ_r. lia.
    + cbn. lia.
Qed.

Fixpoint Pos_is_pow2 (p : positive) : bool :=
  match p with
  | (p'~1)%positive => false
  | (p'~0)%positive => Pos_is_pow2 p'
  | 1%positive      => true
  end.

(** ** Power of two closed upper bound [q <= 2^z] *)

Definition Qbound_le_ZExp2 (q : Q) : Z :=
  match Qnum q with
  (* The -1000 is a compromise between a tight Archimedian and avoiding too large numbers *)
  | Z0 => -1000
  | Zneg p => 0
  | Zpos p => (Z.pos (Pos_log2ceil_plus1 p) - Z.pos (Pos_log2floor_plus1 (Qden q)))%Z
  end.

Lemma Qbound_le_ZExp2_spec : forall (q : Q),
  (q <= 2^(Qbound_le_ZExp2 q))%Q.
Proof.
  intros q.
  destruct q as [num den]; unfold Qbound_le_ZExp2, Qnum; destruct num.
  - intros contra; inversion contra.
  - rewrite Qpower_minus by lra.
    apply Qle_shift_div_l.
      apply Qpower_pos_lt; lra.
    do 2 rewrite Qpower_decomp', Pos_pow_1_r.
    unfold Qle, Qmult, Qnum, Qden.
    rewrite Pos.mul_1_r, Z.mul_1_r.
    pose proof Pos_log2ceil_plus1_spec p as Hnom.
    pose proof Pos_log2floor_plus1_spec den as Hden.

    apply (Zmult_le_reg_r _ _ 2).
        lia.
    replace (Z.pos p * 2 ^ Z.pos (Pos_log2floor_plus1 den) * 2)%Z
      with ((Z.pos p * 2) * 2 ^ Z.pos (Pos_log2floor_plus1 den))%Z by ring.
    replace (2 ^ Z.pos (Pos_log2ceil_plus1 p) * Z.pos den * 2)%Z
      with (2 ^ Z.pos (Pos_log2ceil_plus1 p) * (Z.pos den * 2))%Z by ring.
    apply Z.mul_le_mono_nonneg; lia.
  - intros contra; inversion contra.
Qed.

Definition Qbound_leabs_ZExp2 (q : Q) : Z := Qbound_le_ZExp2 (Qabs q).

Lemma Qbound_leabs_ZExp2_spec : forall (q : Q),
  (Qabs q <= 2^(Qbound_leabs_ZExp2 q))%Q.
Proof.
  intros q.
  unfold Qbound_leabs_ZExp2; apply Qabs_case; intros.
  1,2: apply Qbound_le_ZExp2_spec.
Qed.

(** ** Power of two open upper bound [q < 2^z] and [Qabs q < 2^z] *)

(** Compute a z such that q<2^z.
    z shall be close to as small as possible, but we need a compromise between
    the tighness of the bound and the computation speed and proof complexity.
    Looking just at the log2 of the numerator and denominator, this is a tight bound
    except when the numerator is a power of 2 and the denomintor is not.
    E.g. this return 4/5 < 2^1 instead of 4/5< 2^0.
    If q==0, we return -1000, because as binary integer this has just 10 bits but
    2^-1000 should be smaller than almost any number in practice.
    If numbers are much smaller, computations might be inefficient. *)

Definition Qbound_lt_ZExp2 (q : Q) : Z :=
  match Qnum q with
  (* The -1000 is a compromise between a tight Archimedian and avoiding too large numbers *)
  | Z0 => -1000
  | Zneg p => 0
  | Zpos p => Z.pos_sub (Pos.succ (Pos_log2floor_plus1 p)) (Pos_log2floor_plus1 (Qden q))
  end.

Remark Qbound_lt_ZExp2_test_1 : Qbound_lt_ZExp2 (4#4) = 1%Z. reflexivity. Qed.
Remark Qbound_lt_ZExp2_test_2 : Qbound_lt_ZExp2 (5#4) = 1%Z. reflexivity. Qed.
Remark Qbound_lt_ZExp2_test_3 : Qbound_lt_ZExp2 (4#5) = 1%Z. reflexivity. Qed.
Remark Qbound_lt_ZExp2_test_4 : Qbound_lt_ZExp2 (7#5) = 1%Z. reflexivity. Qed.

Lemma Qbound_lt_ZExp2_spec : forall (q : Q),
  (q < 2^(Qbound_lt_ZExp2 q))%Q.
Proof.
  intros q.
  destruct q as [num den]; unfold Qbound_lt_ZExp2, Qnum; destruct num.
  - reflexivity.
  - (* Todo: A lemma like Pos2Z.add_neg_pos for minus would be nice *)
    change
      (Z.pos_sub (Pos.succ (Pos_log2floor_plus1 p)) (Pos_log2floor_plus1 (Qden (Z.pos p # den))))%Z
    with
      ((Z.pos (Pos.succ (Pos_log2floor_plus1 p)) - Z.pos (Pos_log2floor_plus1 (Qden (Z.pos p # den)))))%Z.
    rewrite Qpower_minus by lra.
    apply Qlt_shift_div_l.
      apply Qpower_pos_lt; lra.
    do 2 rewrite Qpower_decomp', Pos_pow_1_r.
    unfold Qlt, Qmult, Qnum, Qden.
    rewrite Pos.mul_1_r, Z.mul_1_r.
    pose proof Pos_log2floor_plus1_spec p as Hnom.
    pose proof Pos_log2floor_plus1_spec den as Hden.
    apply (Zmult_lt_reg_r _ _ 2).
      lia.
    rewrite Pos2Z.inj_succ, <- Z.add_1_r.
    rewrite Z.pow_add_r by lia.

    replace (Z.pos p * 2 ^ Z.pos (Pos_log2floor_plus1 den) * 2)%Z
      with (2 ^ Z.pos (Pos_log2floor_plus1 den) * (Z.pos p * 2))%Z by ring.
    replace (2 ^ Z.pos (Pos_log2floor_plus1 p) * 2 ^ 1 * Z.pos den * 2)%Z
      with ((Z.pos den * 2) * (2 * 2 ^ Z.pos (Pos_log2floor_plus1 p)))%Z by ring.

    (* ToDo: this is weaker than neccessary: Z.mul_lt_mono_nonneg. *)
    apply Zmult_lt_compat2; lia.
  - cbn.
    (* ToDo: lra could know that negative fractions are negative *)
    assert (Z.neg p # den < 0) as Hnegfrac by (unfold Qlt, Qnum, Qden; lia).
    lra.
Qed.

Definition Qbound_ltabs_ZExp2 (q : Q) : Z := Qbound_lt_ZExp2 (Qabs q).

Lemma Qbound_ltabs_ZExp2_spec : forall (q : Q),
  (Qabs q < 2^(Qbound_ltabs_ZExp2 q))%Q.
Proof.
  intros q.
  unfold Qbound_ltabs_ZExp2; apply Qabs_case; intros.
  1,2: apply Qbound_lt_ZExp2_spec.
Qed.

(** ** Power of 2 open lower bounds for [2^z < q] and [2^z < Qabs q] *)

(** Note: the -2 is required cause of the Qlt limit.
    In case q is a power of two, the lower and upper bound must be a factor of 4 apart *)
Definition Qlowbound_ltabs_ZExp2 (q : Q) : Z := -2 + Qbound_ltabs_ZExp2 q.

Lemma Qlowbound_ltabs_ZExp2_inv: forall q : Q,
    q > 0
 -> Qlowbound_ltabs_ZExp2 q = (- Qbound_ltabs_ZExp2 (/q))%Z.
Proof.
  intros q Hqgt0.
  destruct q as [n d].
  unfold Qlowbound_ltabs_ZExp2, Qbound_ltabs_ZExp2, Qbound_lt_ZExp2, Qnum.
  destruct n.
  - inversion Hqgt0.
  - unfold Qabs, Z.abs, Qinv, Qnum, Qden.
    rewrite -> Z.pos_sub_opp.
    do 2 rewrite <- Pos2Z.add_pos_neg.
    lia.
  - inversion Hqgt0.
Qed.

Lemma Qlowbound_ltabs_ZExp2_opp: forall q : Q,
  (Qlowbound_ltabs_ZExp2 q = Qlowbound_ltabs_ZExp2 (-q))%Z.
Proof.
  intros q.
  destruct q as [[|n|n] d]; reflexivity.
Qed.

Lemma Qlowbound_lt_ZExp2_spec : forall (q : Q) (Hqgt0 : q > 0),
  (2^(Qlowbound_ltabs_ZExp2 q) < q)%Q.
Proof.
  intros q Hqgt0.
  pose proof Qbound_ltabs_ZExp2_spec (/q) as Hspecub.
  rewrite Qlowbound_ltabs_ZExp2_inv by exact Hqgt0.
  rewrite Qpower_opp.
  setoid_rewrite <- (Qinv_involutive q) at 2.
  apply -> Qinv_lt_contravar.
  - rewrite Qabs_pos in Hspecub.
    + exact Hspecub.
    + apply Qlt_le_weak, Qinv_lt_0_compat, Hqgt0.
  - apply Qpower_pos_lt; lra.
  - apply Qinv_lt_0_compat, Hqgt0.
Qed.

Lemma Qlowbound_ltabs_ZExp2_spec : forall (q : Q) (Hqgt0 : ~ q == 0),
  (2^(Qlowbound_ltabs_ZExp2 q) < Qabs q)%Q.
Proof.
  intros q Hqgt0.
  destruct (Q_dec 0 q) as [[H|H]|H].
  - rewrite Qabs_pos by lra.
    apply Qlowbound_lt_ZExp2_spec, H.
  - rewrite Qabs_neg by lra.
    rewrite Qlowbound_ltabs_ZExp2_opp.
    apply Qlowbound_lt_ZExp2_spec.
    lra.
  - lra.
Qed.

(** ** Existential formulations of power of 2 lower and upper bounds *)

Definition QarchimedeanExp2_Z (q : Q)
  :  {z : Z | (q < 2^z)%Q}
  := exist _ (Qbound_lt_ZExp2 q) (Qbound_lt_ZExp2_spec q).

Definition QarchimedeanAbsExp2_Z (q : Q)
  :  {z : Z | (Qabs q < 2^z)%Q}
  := exist _ (Qbound_ltabs_ZExp2 q) (Qbound_ltabs_ZExp2_spec q).

Definition QarchimedeanLowExp2_Z (q : Q) (Hqgt0 : q > 0)
  :  {z : Z | (2^z < q)%Q}
  := exist _ (Qlowbound_ltabs_ZExp2 q) (Qlowbound_lt_ZExp2_spec q Hqgt0).

Definition QarchimedeanLowAbsExp2_Z (q : Q) (Hqgt0 : ~ q == 0)
  :  {z : Z | (2^z < Qabs q)%Q}
  := exist _ (Qlowbound_ltabs_ZExp2 q) (Qlowbound_ltabs_ZExp2_spec q Hqgt0).
