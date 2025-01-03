(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Zpow_facts Qfield Qreduction.

(** * Properties of Qpower_positive *)

(** ** Values of Qpower_positive for specific arguments *)

Lemma Qpower_positive_1 : forall n, Qpower_positive 1 n == 1.
Proof.
induction n;
simpl; try rewrite IHn; reflexivity.
Qed.

Lemma Qpower_positive_0 : forall n, Qpower_positive 0 n == 0.
Proof.
induction n;
simpl; try rewrite IHn; reflexivity.
Qed.

(** ** Relation of Qpower_positive to zero *)

Lemma Qpower_not_0_positive : forall a n, ~a==0 -> ~Qpower_positive a n == 0.
Proof.
intros a n X H.
apply X; clear X.
induction n; simpl in *; try assumption;
destruct (Qmult_integral _ _ H);
try destruct (Qmult_integral _ _ H0); auto.
Qed.

Lemma Qpower_pos_positive : forall p n, 0 <= p -> 0 <= Qpower_positive p n.
Proof.
intros p n Hp.
induction n; simpl; repeat apply Qmult_le_0_compat;assumption.
Qed.

(** ** Qpower_positive and multiplication, exponent subtraction *)

Lemma Qmult_power_positive  : forall a b n, Qpower_positive (a*b) n == (Qpower_positive a n)*(Qpower_positive b n).
Proof.
induction n;
simpl; repeat rewrite IHn; ring.
Qed.

Lemma Qpower_plus_positive : forall a n m, Qpower_positive a (n+m) == (Qpower_positive a n)*(Qpower_positive a m).
Proof.
intros a n m.
unfold Qpower_positive.
apply pow_pos_add.
- apply Q_Setoid.
- apply Qmult_comp.
- apply Qmult_assoc.
Qed.

(** ** Qpower_positive and inversion, division, exponent subtraction *)

Lemma Qinv_power_positive  : forall a n, Qpower_positive (/a) n == /(Qpower_positive a n).
Proof.
induction n;
simpl; repeat (rewrite IHn || rewrite Qinv_mult_distr); reflexivity.
Qed.

Lemma Qpower_minus_positive : forall a (n m:positive),
  (m < n)%positive ->
  Qpower_positive a (n-m)%positive == (Qpower_positive a n)/(Qpower_positive a m).
Proof.
intros a n m H.
destruct (Qeq_dec a 0) as [EQ|NEQ].
- now rewrite EQ, !Qpower_positive_0.
- rewrite <- (Qdiv_mult_l (Qpower_positive a (n - m)) (Qpower_positive a m)) by
   (now apply Qpower_not_0_positive).
  f_equiv.
  rewrite <- Qpower_plus_positive.
  now rewrite Pos.sub_add.
Qed.

(** ** Qpower and exponent multiplication *)

Lemma Qpower_mult_positive : forall a n m,
  Qpower_positive a (n*m) == Qpower_positive (Qpower_positive a n) m.
Proof.
intros a n m.
induction n using Pos.peano_ind.
- reflexivity.
- rewrite Pos.mul_succ_l.
  rewrite <- Pos.add_1_l.
  do 2 rewrite Qpower_plus_positive.
  rewrite IHn.
  rewrite Qmult_power_positive.
  reflexivity.
Qed.

(** ** Qpower_positive decomposition *)

Lemma Qpower_decomp_positive p x y :
  Qpower_positive (x#y) p = x ^ Zpos p # (y ^ p).
Proof.
induction p; intros; simpl Qpower_positive; rewrite ?IHp.
- (* xI *)
  unfold Qmult, Qnum, Qden. f_equal.
  + now rewrite <- Z.pow_twice_r, <- Z.pow_succ_r.
  + apply Pos2Z.inj; rewrite !Pos2Z.inj_mul, !Pos2Z.inj_pow.
    now rewrite <- Z.pow_twice_r, <- Z.pow_succ_r.
- (* xO *)
  unfold Qmult, Qnum, Qden. f_equal.
  + now rewrite <- Z.pow_twice_r.
  + apply Pos2Z.inj; rewrite !Pos2Z.inj_mul, !Pos2Z.inj_pow.
    now rewrite <- Z.pow_twice_r.
- (* xO *)
  now rewrite Z.pow_1_r, Pos.pow_1_r.
Qed.

(* This notation will be deprecated with a planned larger rework of Q lemma naming *)
Notation Qpower_decomp := Qpower_decomp_positive (only parsing).

(** * Properties of Qpower *)

(** ** Values of Qpower for specific arguments *)

Lemma Qpower_0 : forall n, (n<>0)%Z -> 0^n == 0.
Proof.
  intros [|n|n] Hn; try (elim Hn; reflexivity); simpl;
  rewrite Qpower_positive_0; reflexivity.
Qed.

Lemma Qpower_1 : forall n, 1^n == 1.
Proof.
  intros [|n|n]; simpl; try rewrite Qpower_positive_1; reflexivity.
Qed.

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

(** ** Relation of Qpower to zero *)

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

Lemma Qpower_0_le : forall (p : Q) (n : Z), 0 <= p -> 0 <= p^n.
Proof.
  intros p [|n|n] Hp; simpl; try discriminate;
  try apply Qinv_le_0_compat;  apply Qpower_pos_positive; assumption.
Qed.

(* This notation will be deprecated with a planned larger rework of Q lemma naming *)
Notation Qpower_pos := Qpower_0_le (only parsing).

Lemma Qpower_0_lt: forall (a : Q) (z : Z), 0 < a -> 0 < Qpower a z.
Proof.
  intros q z Hpos.
  pose proof Qpower_pos q z (Qlt_le_weak 0 q Hpos) as H1.
  pose proof Qpower_not_0 q z as H2.
  pose proof Qlt_not_eq 0 q Hpos as H3.
  specialize (H2 (Qnot_eq_sym _ _ H3)); clear H3.
  apply Qnot_eq_sym in H2.
  apply Qlt_leneq; split; assumption.
Qed.

(** ** Relation of Qpower to 1 *)

Lemma Qpower_1_lt_pos:
  forall (q : Q) (n : positive), (1<q)%Q -> (1 < q ^ (Z.pos n))%Q.
Proof.
  intros q n Hq.
  induction n.
  - cbn in *.
    apply Qmult_lt_1_compat. 1:assumption.
    apply Qmult_lt_1_compat; assumption.
  - cbn in *.
    apply Qmult_lt_1_compat; assumption.
  - cbn; assumption.
Qed.

Lemma Qpower_1_lt:
  forall (q : Q) (n : Z), (1<q)%Q -> (0<n)%Z -> (1 < q ^ n)%Q.
Proof.
  intros q n Hq Hn.
  destruct n.
  - inversion Hn.
  - apply Qpower_1_lt_pos; assumption.
  - discriminate (Z.lt_trans _ _ _ Hn (Pos2Z.neg_is_neg p)).
Qed.

Lemma Qpower_1_le_pos:
  forall (q : Q) (n : positive), (1<=q)%Q -> (1 <= q ^ (Z.pos n))%Q.
Proof.
  intros q n Hq.
  induction n.
  - cbn in *.
    apply Qmult_le_1_compat. 1:assumption.
    apply Qmult_le_1_compat; assumption.
  - cbn in *.
    apply Qmult_le_1_compat; assumption.
  - cbn; assumption.
Qed.

Lemma Qpower_1_le:
  forall (q : Q) (n : Z), (1<=q)%Q -> (0<=n)%Z -> (1 <= q ^ n)%Q.
Proof.
  intros q n Hq Hn.
  destruct n.
  - apply Qle_refl.
  - apply Qpower_1_le_pos; assumption.
  - discriminate (Z.le_lt_trans _ _ _ Hn (Pos2Z.neg_is_neg p)).
Qed.

(** ** Qpower and multiplication, exponent addition *)

Lemma Qmult_power : forall a b n, (a*b)^n == a^n*b^n.
Proof.
  intros a b [|n|n]; simpl;
  try rewrite Qmult_power_positive;
  try rewrite Qinv_mult_distr;
  reflexivity.
Qed.

Lemma Qpower_plus : forall a n m, ~a==0 -> a^(n+m) == a^n*a^m.
Proof.
intros a [|n|n] [|m|m] H; simpl; try ring;
try rewrite Qpower_plus_positive;
try apply Qinv_mult_distr; try reflexivity;
rewrite ?Z.pos_sub_spec;
case Pos.compare_spec; intros H0; simpl; subst;
 try rewrite Qpower_minus_positive;
 try (field; try split; apply Qpower_not_0_positive);
 assumption.
Qed.

Lemma Qpower_plus' : forall a n m, (n+m <> 0)%Z -> a^(n+m) == a^n*a^m.
Proof.
intros a n m H.
destruct (Qeq_dec a 0)as [X|X].
- rewrite X.
  rewrite Qpower_0 by assumption.
  destruct n; destruct m; try (elim H; reflexivity);
    simpl; repeat rewrite Qpower_positive_0; ring_simplify;
    reflexivity.
- apply Qpower_plus.
  assumption.
Qed.

(** ** Qpower and inversion, division, exponent subtraction *)

Lemma Qinv_power : forall a n, (/a)^n == /a^n.
Proof.
  intros a [|n|n]; simpl;
  try rewrite Qinv_power_positive;
  reflexivity.
Qed.

Lemma Qdiv_power : forall a b n, (a/b)^n == (a^n/b^n).
Proof.
unfold Qdiv.
intros a b n.
rewrite Qmult_power.
rewrite Qinv_power.
reflexivity.
Qed.

Lemma Qinv_power_n : forall n p, (1#p)^n == /(inject_Z (Zpos p))^n.
Proof.
intros n p.
rewrite Qmake_Qdiv.
rewrite Qdiv_power.
rewrite Qpower_1.
unfold Qdiv.
ring.
Qed.

Lemma Qpower_opp : forall a n, a^(-n) == /a^n.
Proof.
intros a [|n|n]; simpl; try reflexivity.
symmetry; apply Qinv_involutive.
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
  rewrite <- (Qinv_pos b a), Qinv_power.
  reflexivity.
Qed.

Lemma Qpower_minus_neg: forall (a b : positive) (n m : Z),
  (Z.neg a#b) ^ (n - m) == (Z.neg a#b) ^ n * (Z.neg b#a) ^ m.
Proof.
  intros a b n m.
  rewrite Qpower_minus by discriminate.
  rewrite <- (Qinv_neg b a), Qinv_power.
  reflexivity.
Qed.

(** ** Qpower and exponent multiplication *)

Lemma Qpower_mult : forall a n m, a^(n*m) ==  (a^n)^m.
Proof.
intros a [|n|n] [|m|m]; simpl;
 try rewrite Qpower_positive_1;
 try rewrite Qpower_mult_positive;
 try rewrite Qinv_power_positive;
 try rewrite Qinv_involutive;
 try reflexivity.
Qed.

(** ** Qpower decomposition *)

Lemma Qpower_decomp_pos: forall (p : positive) (a : Z) (b : positive),
  (a # b) ^ (Z.pos p) == a ^ (Z.pos p) # (b ^ p)%positive.
Proof.
  intros p a b.
  pose proof Qpower_decomp_positive p a b.
  cbn; rewrite H; reflexivity.
Qed.

Lemma Qpower_decomp_neg_pos: forall (p a b: positive),
  (Z.pos a # b) ^ (Z.neg p) == (Z.pos b) ^ (Z.pos p) # (a ^ p)%positive.
Proof.
  intros p a b.
  cbn.
  rewrite <- Qinv_power_positive, Qinv_pos.
  rewrite Qpower_decomp_positive.
  reflexivity.
Qed.

Lemma Qpower_decomp_neg_neg: forall (p a b: positive),
  (Z.neg a # b) ^ (Z.neg p) == (Z.neg b) ^ (Z.pos p) # (a ^ p)%positive.
Proof.
  intros p a b.
  cbn.
  rewrite <- Qinv_power_positive, Qinv_neg.
  rewrite Qpower_decomp_positive.
  reflexivity.
Qed.

(** ** Compatibility of Qpower with relational operators *)

Lemma Qpower_lt_compat_l:
  forall (q : Q) (n m : Z), (n < m)%Z -> (1<q)%Q -> (q ^ n < q ^ m)%Q.
Proof.
  intros q n m Hnm Hq.
  replace m with (n+(m-n))%Z by ring.
  rewrite Qpower_plus, <- Qmult_1_r, <- Qmult_assoc.
    2: { intros Habsurd. rewrite Habsurd in Hq. discriminate Hq. }
  rewrite Qmult_lt_l, Qmult_1_l.
    2: { apply Qpower_0_lt. exact (Qlt_trans 0 1 q ltac:(reflexivity) Hq). }
  remember (m-n)%Z as k.
  apply Qpower_1_lt.
  - exact Hq.
  - rewrite Heqk; apply Z.lt_0_sub, Hnm.
Qed.

Lemma Qpower_le_compat_l:
  forall (q : Q) (n m : Z), (n <= m)%Z -> (1<=q)%Q -> (q ^ n <= q ^ m)%Q.
Proof.
  intros q n m Hnm Hq.
  replace m with (n+(m-n))%Z by ring.
  rewrite Qpower_plus, <- Qmult_1_r, <- Qmult_assoc.
    2: { intros Habsurd. rewrite Habsurd in Hq. apply Hq. reflexivity. }
  rewrite Qmult_le_l, Qmult_1_l.
    2: { apply Qpower_0_lt. exact (Qlt_le_trans 0 1 q ltac:(reflexivity) Hq). }
  remember (m-n)%Z as k.
  apply Qpower_1_le.
  - exact Hq.
  - rewrite Heqk; apply Z.le_0_sub, Hnm.
Qed.

Lemma Qpower_lt_compat_l_inv:
  forall (q : Q) (n m : Z), (q ^ n < q ^ m)%Q -> (1<q)%Q -> (n < m)%Z.
Proof.
  intros q n m Hnm Hq.
  destruct (Z.ltb_spec n m) as [Hd|Hd].
  - assumption.
  - pose proof Qpower_le_compat_l q m n Hd (Qlt_le_weak _ _ Hq) as Hnm'.
    pose proof Qlt_le_trans _ _ _ Hnm Hnm' as Habsurd.
    destruct (Qlt_irrefl _ Habsurd).
Qed.

Lemma Qpower_le_compat_l_inv:
  forall (q : Q) (n m : Z), (q ^ n <= q ^ m)%Q -> (1<q)%Q -> (n <= m)%Z.
Proof.
  intros q n m Hnm Hq.
  destruct (Z.ltb_spec m n) as [Hd|Hd].
  - pose proof Qpower_lt_compat_l q m n Hd Hq as Hnm'.
    pose proof Qle_lt_trans _ _ _ Hnm Hnm' as Habsurd.
    destruct (Qlt_irrefl _ Habsurd).
  - assumption.
Qed.

(** ** Qpower and inject_Z *)

Lemma Zpower_Qpower : forall (a n:Z), (0<=n)%Z -> inject_Z (a^n) == (inject_Z a)^n.
Proof.
intros a [|n|n] H;[reflexivity| |elim H; reflexivity].
induction n using Pos.peano_ind.
- replace (a^1)%Z with a by ring.
  ring.
- rewrite Pos2Z.inj_succ.
  unfold Z.succ.
  rewrite Zpower_exp; auto with *; try discriminate.
  rewrite Qpower_plus' by discriminate.
  rewrite <- IHn by discriminate.
  replace (a^Zpos n*a^1)%Z with (a^Zpos n*a)%Z by ring.
  ring_simplify.
  reflexivity.
Qed.

(** ** Square *)

Lemma Qsqr_nonneg : forall a, 0 <= a^2.
Proof.
intros a.
destruct (Qlt_le_dec 0 a) as [A|A].
- apply (Qmult_le_0_compat a a);
    (apply Qlt_le_weak; assumption).
- setoid_replace (a^2) with ((-a)*(-a)) by ring.
  rewrite Qle_minus_iff in A.
  setoid_replace (0+ - a) with (-a) in A by ring.
  apply Qmult_le_0_compat; assumption.
Qed.

(** ** Power of 2 positive upper bound *)

Lemma Qarchimedean_power2_pos : forall q : Q,
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
