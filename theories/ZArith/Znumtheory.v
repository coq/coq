(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Require Import Wf_nat.

(** For compatibility reasons, this Open Scope isn't local as it should *)

Open Scope Z_scope.

(** This file contains some notions of number theory upon Z numbers:
     - a divisibility predicate [Z.divide]
     - a gcd predicate [gcd]
     - Euclid algorithm [euclid]
     - a relatively prime predicate [rel_prime]
     - a prime predicate [prime]
     - properties of the efficient [Z.gcd] function
*)

Notation Zgcd := Z.gcd (compat "8.7").
Notation Zggcd := Z.ggcd (compat "8.7").
Notation Zggcd_gcd := Z.ggcd_gcd (compat "8.7").
Notation Zggcd_correct_divisors := Z.ggcd_correct_divisors (compat "8.7").
Notation Zgcd_divide_l := Z.gcd_divide_l (compat "8.7").
Notation Zgcd_divide_r := Z.gcd_divide_r (compat "8.7").
Notation Zgcd_greatest := Z.gcd_greatest (compat "8.7").
Notation Zgcd_nonneg := Z.gcd_nonneg (compat "8.7").
Notation Zggcd_opp := Z.ggcd_opp (compat "8.7").

(** The former specialized inductive predicate [Z.divide] is now
    a generic existential predicate. *)

Notation Zdivide := Z.divide (compat "8.7").

(** Its former constructor is now a pseudo-constructor. *)

Definition Zdivide_intro a b q (H:b=q*a) : Z.divide a b := ex_intro _ q H.

(** Results concerning divisibility*)

Notation Zdivide_refl := Z.divide_refl (compat "8.7").
Notation Zone_divide := Z.divide_1_l (only parsing).
Notation Zdivide_0 := Z.divide_0_r (only parsing).
Notation Zmult_divide_compat_l := Z.mul_divide_mono_l (only parsing).
Notation Zmult_divide_compat_r := Z.mul_divide_mono_r (only parsing).
Notation Zdivide_plus_r := Z.divide_add_r (only parsing).
Notation Zdivide_minus_l := Z.divide_sub_r (only parsing).
Notation Zdivide_mult_l := Z.divide_mul_l (only parsing).
Notation Zdivide_mult_r := Z.divide_mul_r (only parsing).
Notation Zdivide_factor_r := Z.divide_factor_l (only parsing).
Notation Zdivide_factor_l := Z.divide_factor_r (only parsing).

Lemma Zdivide_opp_r a b : (a | b) -> (a | - b).
Proof. apply Z.divide_opp_r. Qed.

Lemma Zdivide_opp_r_rev a b : (a | - b) -> (a | b).
Proof. apply Z.divide_opp_r. Qed.

Lemma Zdivide_opp_l a b : (a | b) -> (- a | b).
Proof. apply Z.divide_opp_l. Qed.

Lemma Zdivide_opp_l_rev a b : (- a | b) -> (a | b).
Proof. apply Z.divide_opp_l. Qed.

Theorem Zdivide_Zabs_l a b : (Z.abs a | b) -> (a | b).
Proof. apply Z.divide_abs_l. Qed.

Theorem Zdivide_Zabs_inv_l a b : (a | b) -> (Z.abs a | b).
Proof. apply Z.divide_abs_l. Qed.

Hint Resolve Z.divide_refl Z.divide_1_l Z.divide_0_r: zarith.
Hint Resolve Z.mul_divide_mono_l Z.mul_divide_mono_r: zarith.
Hint Resolve Z.divide_add_r Zdivide_opp_r Zdivide_opp_r_rev Zdivide_opp_l
  Zdivide_opp_l_rev Z.divide_sub_r Z.divide_mul_l Z.divide_mul_r
  Z.divide_factor_l Z.divide_factor_r: zarith.

(** Auxiliary result. *)

Lemma Zmult_one x y : x >= 0 -> x * y = 1 -> x = 1.
Proof.
 Z.swap_greater. apply Z.eq_mul_1_nonneg.
Qed.

(** Only [1] and [-1] divide [1]. *)

Notation Zdivide_1 := Z.divide_1_r (only parsing).

(** If [a] divides [b] and [b] divides [a] then [a] is [b] or [-b]. *)

Notation Zdivide_antisym := Z.divide_antisym (compat "8.7").
Notation Zdivide_trans := Z.divide_trans (compat "8.7").

(** If [a] divides [b] and [b<>0] then [|a| <= |b|]. *)

Lemma Zdivide_bounds a b : (a | b) -> b <> 0 -> Z.abs a <= Z.abs b.
Proof.
 intros H Hb.
 rewrite <- Z.divide_abs_l, <- Z.divide_abs_r in H.
 apply Z.abs_pos in Hb.
 now apply Z.divide_pos_le.
Qed.

(** [Z.divide] can be expressed using [Z.modulo]. *)

Lemma Zmod_divide : forall a b, b<>0 -> a mod b = 0 -> (b | a).
Proof.
 apply Z.mod_divide.
Qed.

Lemma Zdivide_mod : forall a b, (b | a) -> a mod b = 0.
Proof.
 intros a b (c,->); apply Z_mod_mult.
Qed.

(** [Z.divide] is hence decidable *)

Lemma Zdivide_dec a b : {(a | b)} + {~ (a | b)}.
Proof.
 destruct (Z.eq_dec a 0) as [Ha|Ha].
  destruct (Z.eq_dec b 0) as [Hb|Hb].
   left; subst; apply Z.divide_0_r.
   right. subst. contradict Hb. now apply Z.divide_0_l.
  destruct (Z.eq_dec (b mod a) 0).
   left. now apply Z.mod_divide.
   right. now rewrite <- Z.mod_divide.
Defined.

Theorem Zdivide_Zdiv_eq a b : 0 < a -> (a | b) ->  b = a * (b / a).
Proof.
 intros Ha H.
 rewrite (Z.div_mod b a) at 1; auto with zarith.
 rewrite Zdivide_mod; auto with zarith.
Qed.

Theorem Zdivide_Zdiv_eq_2 a b c :
 0 < a -> (a | b) -> (c * b) / a = c * (b / a).
Proof.
 intros. apply Z.divide_div_mul_exact; auto with zarith.
Qed.

Theorem Zdivide_le: forall a b : Z,
 0 <= a -> 0 < b -> (a | b) ->  a <= b.
Proof.
 intros. now apply Z.divide_pos_le.
Qed.

Theorem Zdivide_Zdiv_lt_pos a b :
 1 < a -> 0 < b -> (a | b) ->  0 < b / a < b .
Proof.
  intros H1 H2 H3; split.
  apply Z.mul_pos_cancel_l with a; auto with zarith.
  rewrite <- Zdivide_Zdiv_eq; auto with zarith.
  now apply Z.div_lt.
Qed.

Lemma Zmod_div_mod n m a:
 0 < n -> 0 < m -> (n | m) -> a mod n = (a mod m) mod n.
Proof.
  intros H1 H2 (p,Hp).
  rewrite (Z.div_mod a m) at 1; auto with zarith.
  rewrite Hp at 1.
  rewrite Z.mul_shuffle0, Z.add_comm, Z.mod_add; auto with zarith.
Qed.

Lemma Zmod_divide_minus a b c:
 0 < b -> a mod b = c -> (b | a - c).
Proof.
  intros H H1. apply Z.mod_divide; auto with zarith.
  rewrite Zminus_mod; auto with zarith.
  rewrite H1. rewrite <- (Z.mod_small c b) at 1.
  rewrite Z.sub_diag, Z.mod_0_l; auto with zarith.
  subst. now apply Z.mod_pos_bound.
Qed.

Lemma Zdivide_mod_minus a b c:
 0 <= c < b -> (b | a - c) -> a mod b = c.
Proof.
  intros (H1, H2) H3.
  assert (0 < b) by Z.order.
  replace a with ((a - c) + c); auto with zarith.
  rewrite Z.add_mod; auto with zarith.
  rewrite (Zdivide_mod (a-c) b); try rewrite Z.add_0_l; auto with zarith.
  rewrite Z.mod_mod; try apply Zmod_small; auto with zarith.
Qed.

(** * Greatest common divisor (gcd). *)

(** There is no unicity of the gcd; hence we define the predicate
    [Zis_gcd a b g] expressing that [g] is a gcd of [a] and [b].
    (We show later that the [gcd] is actually unique if we discard its sign.) *)

Inductive Zis_gcd (a b g:Z) : Prop :=
 Zis_gcd_intro :
  (g | a) ->
  (g | b) ->
  (forall x, (x | a) -> (x | b) -> (x | g)) ->
  Zis_gcd a b g.

(** Trivial properties of [gcd] *)

Lemma Zis_gcd_sym : forall a b d, Zis_gcd a b d -> Zis_gcd b a d.
Proof.
  induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_0 : forall a, Zis_gcd a 0 a.
Proof.
  constructor; auto with zarith.
Qed.

Lemma Zis_gcd_1 : forall a, Zis_gcd a 1 1.
Proof.
  constructor; auto with zarith.
Qed.

Lemma Zis_gcd_refl : forall a, Zis_gcd a a a.
Proof.
  constructor; auto with zarith.
Qed.

Lemma Zis_gcd_minus : forall a b d, Zis_gcd a (- b) d -> Zis_gcd b a d.
Proof.
  induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_opp : forall a b d, Zis_gcd a b d -> Zis_gcd b a (- d).
Proof.
  induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_0_abs a : Zis_gcd 0 a (Z.abs a).
Proof.
  apply Zabs_ind.
  intros; apply Zis_gcd_sym; apply Zis_gcd_0; auto.
  intros; apply Zis_gcd_opp; apply Zis_gcd_0; auto.
Qed.

Hint Resolve Zis_gcd_sym Zis_gcd_0 Zis_gcd_minus Zis_gcd_opp: zarith.

Theorem Zis_gcd_unique: forall a b c d : Z,
 Zis_gcd a b c -> Zis_gcd a b d ->  c = d \/ c = (- d).
Proof.
intros a b c d [Hc1 Hc2 Hc3] [Hd1 Hd2 Hd3].
assert (c|d) by auto.
assert (d|c) by auto.
apply Z.divide_antisym; auto.
Qed.


(** * Extended Euclid algorithm. *)

(** Euclid's algorithm to compute the [gcd] mainly relies on
    the following property. *)

Lemma Zis_gcd_for_euclid :
  forall a b d q:Z, Zis_gcd b (a - q * b) d -> Zis_gcd a b d.
Proof.
  simple induction 1; constructor; intuition.
  replace a with (a - q * b + q * b). auto with zarith. ring.
Qed.

Lemma Zis_gcd_for_euclid2 :
  forall b d q r:Z, Zis_gcd r b d -> Zis_gcd b (b * q + r) d.
Proof.
  simple induction 1; constructor; intuition.
  apply H2; auto.
  replace r with (b * q + r - b * q). auto with zarith. ring.
Qed.

(** We implement the extended version of Euclid's algorithm,
    i.e. the one computing Bezout's coefficients as it computes
    the [gcd]. We follow the algorithm given in Knuth's
    "Art of Computer Programming", vol 2, page 325. *)

Section extended_euclid_algorithm.

  Variables a b : Z.

  (** The specification of Euclid's algorithm is the existence of
      [u], [v] and [d] such that [ua+vb=d] and [(gcd a b d)]. *)

  Inductive Euclid : Set :=
    Euclid_intro :
    forall u v d:Z, u * a + v * b = d -> Zis_gcd a b d -> Euclid.

  (** The recursive part of Euclid's algorithm uses well-founded
      recursion of non-negative integers. It maintains 6 integers
      [u1,u2,u3,v1,v2,v3] such that the following invariant holds:
      [u1*a+u2*b=u3] and [v1*a+v2*b=v3] and [gcd(u3,v3)=gcd(a,b)].
      *)

  Lemma euclid_rec :
    forall v3:Z,
      0 <= v3 ->
      forall u1 u2 u3 v1 v2:Z,
	u1 * a + u2 * b = u3 ->
	v1 * a + v2 * b = v3 ->
	(forall d:Z, Zis_gcd u3 v3 d -> Zis_gcd a b d) -> Euclid.
  Proof.
    intros v3 Hv3; generalize Hv3; pattern v3.
    apply Zlt_0_rec.
    clear v3 Hv3; intros.
    destruct (Z_zerop x) as [Heq|Hneq].
    apply Euclid_intro with (u := u1) (v := u2) (d := u3).
    assumption.
    apply H3.
    rewrite Heq; auto with zarith.
    set (q := u3 / x) in *.
    assert (Hq : 0 <= u3 - q * x < x).
    replace (u3 - q * x) with (u3 mod x).
    apply Z_mod_lt; omega.
    assert (xpos : x > 0). omega.
    generalize (Z_div_mod_eq u3 x xpos).
    unfold q.
    intro eq; pattern u3 at 2; rewrite eq; ring.
    apply (H (u3 - q * x) Hq (proj1 Hq) v1 v2 x (u1 - q * v1) (u2 - q * v2)).
    tauto.
    replace ((u1 - q * v1) * a + (u2 - q * v2) * b) with
      (u1 * a + u2 * b - q * (v1 * a + v2 * b)).
    rewrite H1; rewrite H2; trivial.
    ring.
    intros; apply H3.
    apply Zis_gcd_for_euclid with q; assumption.
    assumption.
  Qed.

  (** We get Euclid's algorithm by applying [euclid_rec] on
      [1,0,a,0,1,b] when [b>=0] and [1,0,a,0,-1,-b] when [b<0]. *)

  Lemma euclid : Euclid.
  Proof.
    case (Z_le_gt_dec 0 b); intro.
    intros;
      apply euclid_rec with
	(u1 := 1) (u2 := 0) (u3 := a) (v1 := 0) (v2 := 1) (v3 := b);
	auto with zarith; ring.
    intros;
      apply euclid_rec with
	(u1 := 1) (u2 := 0) (u3 := a) (v1 := 0) (v2 := -1) (v3 := - b);
	auto with zarith; try ring.
  Qed.

End extended_euclid_algorithm.

Theorem Zis_gcd_uniqueness_apart_sign :
  forall a b d d':Z, Zis_gcd a b d -> Zis_gcd a b d' -> d = d' \/ d = - d'.
Proof.
  simple induction 1.
  intros H1 H2 H3; simple induction 1; intros.
  generalize (H3 d' H4 H5); intro Hd'd.
  generalize (H6 d H1 H2); intro Hdd'.
  exact (Z.divide_antisym d d' Hdd' Hd'd).
Qed.

(** * Bezout's coefficients *)

Inductive Bezout (a b d:Z) : Prop :=
  Bezout_intro : forall u v:Z, u * a + v * b = d -> Bezout a b d.

(** Existence of Bezout's coefficients for the [gcd] of [a] and [b] *)

Lemma Zis_gcd_bezout : forall a b d:Z, Zis_gcd a b d -> Bezout a b d.
Proof.
  intros a b d Hgcd.
  elim (euclid a b); intros u v d0 e g.
  generalize (Zis_gcd_uniqueness_apart_sign a b d d0 Hgcd g).
  intro H; elim H; clear H; intros.
  apply Bezout_intro with u v.
  rewrite H; assumption.
  apply Bezout_intro with (- u) (- v).
  rewrite H; rewrite <- e; ring.
Qed.

(** gcd of [ca] and [cb] is [c gcd(a,b)]. *)

Lemma Zis_gcd_mult :
  forall a b c d:Z, Zis_gcd a b d -> Zis_gcd (c * a) (c * b) (c * d).
Proof.
  intros a b c d; simple induction 1. constructor; auto with zarith.
  intros x Ha Hb.
  elim (Zis_gcd_bezout a b d H). intros u v Huv.
  elim Ha; intros a' Ha'.
  elim Hb; intros b' Hb'.
  apply Zdivide_intro with (u * a' + v * b').
  rewrite <- Huv.
  replace (c * (u * a + v * b)) with (u * (c * a) + v * (c * b)).
  rewrite Ha'; rewrite Hb'; ring.
  ring.
Qed.


(** * Relative primality *)

Definition rel_prime (a b:Z) : Prop := Zis_gcd a b 1.

(** Bezout's theorem: [a] and [b] are relatively prime if and
    only if there exist [u] and [v] such that [ua+vb = 1]. *)

Lemma rel_prime_bezout : forall a b:Z, rel_prime a b -> Bezout a b 1.
Proof.
  intros a b; exact (Zis_gcd_bezout a b 1).
Qed.

Lemma bezout_rel_prime : forall a b:Z, Bezout a b 1 -> rel_prime a b.
Proof.
  simple induction 1; constructor; auto with zarith.
  intros. rewrite <- H0; auto with zarith.
Qed.

(** Gauss's theorem: if [a] divides [bc] and if [a] and [b] are
    relatively prime, then [a] divides [c]. *)

Theorem Gauss : forall a b c:Z, (a | b * c) -> rel_prime a b -> (a | c).
Proof.
  intros. elim (rel_prime_bezout a b H0); intros.
  replace c with (c * 1); [ idtac | ring ].
  rewrite <- H1.
  replace (c * (u * a + v * b)) with (c * u * a + v * (b * c));
    [ eauto with zarith | ring ].
Qed.

(** If [a] is relatively prime to [b] and [c], then it is to [bc] *)

Lemma rel_prime_mult :
  forall a b c:Z, rel_prime a b -> rel_prime a c -> rel_prime a (b * c).
Proof.
  intros a b c Hb Hc.
  elim (rel_prime_bezout a b Hb); intros.
  elim (rel_prime_bezout a c Hc); intros.
  apply bezout_rel_prime.
  apply Bezout_intro with
    (u := u * u0 * a + v0 * c * u + u0 * v * b) (v := v * v0).
  rewrite <- H.
  replace (u * a + v * b) with ((u * a + v * b) * 1); [ idtac | ring ].
  rewrite <- H0.
  ring.
Qed.

Lemma rel_prime_cross_prod :
  forall a b c d:Z,
    rel_prime a b ->
    rel_prime c d -> b > 0 -> d > 0 -> a * d = b * c -> a = c /\ b = d.
Proof.
  intros a b c d; intros.
  elim (Z.divide_antisym b d).
  split; auto with zarith.
  rewrite H4 in H3.
  rewrite Z.mul_comm in H3.
  apply Z.mul_reg_l with d; auto with zarith.
  intros; omega.
  apply Gauss with a.
  rewrite H3.
  auto with zarith.
  red; auto with zarith.
  apply Gauss with c.
  rewrite Z.mul_comm.
  rewrite <- H3.
  auto with zarith.
  red; auto with zarith.
Qed.

(** After factorization by a gcd, the original numbers are relatively prime. *)

Lemma Zis_gcd_rel_prime :
  forall a b g:Z,
    b > 0 -> g >= 0 -> Zis_gcd a b g -> rel_prime (a / g) (b / g).
Proof.
  intros a b g; intros.
  assert (g <> 0).
  intro.
  elim H1; intros.
  elim H4; intros.
  rewrite H2 in H6; subst b; omega.
  unfold rel_prime.
  destruct H1.
  destruct H1 as (a',H1).
  destruct H3 as (b',H3).
  replace (a/g) with a';
    [|rewrite H1; rewrite Z_div_mult; auto with zarith].
  replace (b/g) with b';
    [|rewrite H3; rewrite Z_div_mult; auto with zarith].
  constructor.
  exists a'; auto with zarith.
  exists b'; auto with zarith.
  intros x (xa,H5) (xb,H6).
  destruct (H4 (x*g)) as (x',Hx').
  exists xa; rewrite Z.mul_assoc; rewrite <- H5; auto.
  exists xb; rewrite Z.mul_assoc; rewrite <- H6; auto.
  replace g with (1*g) in Hx'; auto with zarith.
  do 2 rewrite Z.mul_assoc in Hx'.
  apply Z.mul_reg_r in Hx'; trivial.
  rewrite Z.mul_1_r in Hx'.
  exists x'; auto with zarith.
Qed.

Theorem rel_prime_sym: forall a b, rel_prime a b -> rel_prime b a.
Proof.
  intros a b H; auto with zarith.
  red; apply Zis_gcd_sym; auto with zarith.
Qed.

Theorem rel_prime_div: forall p q r,
 rel_prime p q -> (r | p) -> rel_prime r q.
Proof.
  intros p q r H (u, H1); subst.
  inversion_clear H as [H1 H2 H3].
  red; apply Zis_gcd_intro; try apply Z.divide_1_l.
  intros x H4 H5; apply H3; auto.
  apply Z.divide_mul_r; auto.
Qed.

Theorem rel_prime_1: forall n, rel_prime 1 n.
Proof.
  intros n; red; apply Zis_gcd_intro; auto.
  exists 1; auto with zarith.
  exists n; auto with zarith.
Qed.

Theorem not_rel_prime_0: forall n, 1 < n -> ~ rel_prime 0 n.
Proof.
  intros n H H1; absurd (n = 1 \/ n = -1).
  intros [H2 | H2]; subst; contradict H; auto with zarith.
  case (Zis_gcd_unique  0 n n 1); auto.
  apply Zis_gcd_intro; auto.
  exists 0; auto with zarith.
  exists 1; auto with zarith.
Qed.

Theorem rel_prime_mod: forall p q, 0 < q ->
 rel_prime p q -> rel_prime (p mod q) q.
Proof.
  intros p q H H0.
  assert (H1: Bezout p q 1).
  apply rel_prime_bezout; auto.
  inversion_clear H1 as [q1 r1 H2].
  apply bezout_rel_prime.
  apply Bezout_intro with q1  (r1 + q1 * (p / q)).
  rewrite <- H2.
  pattern p at 3; rewrite (Z_div_mod_eq p q); try ring; auto with zarith.
Qed.

Theorem rel_prime_mod_rev: forall p q, 0 < q ->
 rel_prime (p mod q) q -> rel_prime p q.
Proof.
  intros p q H H0.
  rewrite (Z_div_mod_eq p q); auto with zarith; red.
  apply Zis_gcd_sym; apply Zis_gcd_for_euclid2; auto with zarith.
Qed.

Theorem Zrel_prime_neq_mod_0: forall a b, 1 < b -> rel_prime a b -> a mod b <> 0.
Proof.
  intros a b H H1 H2.
  case (not_rel_prime_0 _ H).
  rewrite <- H2.
  apply rel_prime_mod; auto with zarith.
Qed.

(** * Primality *)

Inductive prime (p:Z) : Prop :=
  prime_intro :
    1 < p -> (forall n:Z, 1 <= n < p -> rel_prime n p) -> prime p.

(** The sole divisors of a prime number [p] are [-1], [1], [p] and [-p]. *)

Lemma prime_divisors :
  forall p:Z,
    prime p -> forall a:Z, (a | p) -> a = -1 \/ a = 1 \/ a = p \/ a = - p.
Proof.
  destruct 1; intros.
  assert
    (a = - p \/ - p < a < -1 \/ a = -1 \/ a = 0 \/ a = 1 \/ 1 < a < p \/ a = p).
  { assert (Z.abs a <= Z.abs p) as H2.
      apply Zdivide_bounds; [ assumption | omega ].
    revert H2.
    pattern (Z.abs a); apply Zabs_ind; pattern (Z.abs p); apply Zabs_ind;
    intros; omega. }
  intuition idtac.
  (* -p < a < -1 *)
  - absurd (rel_prime (- a) p); intuition.
    inversion H2.
    assert (- a | - a) by auto with zarith.
    assert (- a | p) by auto with zarith.
    apply H7, Z.divide_1_r in H8; intuition.
  (* a = 0 *)
  - inversion H1. subst a; omega.
  (* 1 < a < p *)
  - absurd (rel_prime a p); intuition.
    inversion H2.
    assert (a | a) by auto with zarith.
    assert (a | p) by auto with zarith.
    apply H7, Z.divide_1_r in H8; intuition.
Qed.

(** A prime number is relatively prime with any number it does not divide *)

Lemma prime_rel_prime :
  forall p:Z, prime p -> forall a:Z, ~ (p | a) -> rel_prime p a.
Proof.
  intros; constructor; intros; auto with zarith.
  apply prime_divisors in H1; intuition; subst; auto with zarith.
  - absurd (p | a); auto with zarith.
  - absurd (p | a); intuition.
Qed.

Hint Resolve prime_rel_prime: zarith.

(** As a consequence, a prime number is relatively prime with smaller numbers *)

Theorem rel_prime_le_prime:
 forall a p, prime p -> 1 <=  a < p -> rel_prime a p.
Proof.
  intros a p Hp [H1 H2].
  apply rel_prime_sym; apply prime_rel_prime; auto.
  intros [q Hq]; subst a.
  case (Z.le_gt_cases q 0); intros Hl.
  absurd (q * p <= 0 * p); auto with zarith.
  absurd (1 * p <= q * p); auto with zarith.
Qed.


(** If a prime [p] divides [ab] then it divides either [a] or [b] *)

Lemma prime_mult :
  forall p:Z, prime p -> forall a b:Z, (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intro p; simple induction 1; intros.
  case (Zdivide_dec p a); intuition.
  right; apply Gauss with a; auto with zarith.
Qed.

Lemma not_prime_0: ~ prime 0.
Proof.
  intros H1; case (prime_divisors _ H1 2); auto with zarith.
Qed.

Lemma not_prime_1: ~ prime 1.
Proof.
  intros H1; absurd (1 < 1); auto with zarith.
  inversion H1; auto.
Qed.

Lemma prime_2: prime 2.
Proof.
  apply prime_intro; auto with zarith.
  intros n (H,H'); Z.le_elim H; auto with zarith.
  - contradict H'; auto with zarith.
  - subst n. constructor; auto with zarith.
Qed.

Theorem prime_3: prime 3.
Proof.
  apply prime_intro; auto with zarith.
  intros n (H,H'); Z.le_elim H; auto with zarith.
  - replace n with 2 by omega.
    constructor; auto with zarith.
    intros x (q,Hq) (q',Hq').
    exists (q' - q). ring_simplify. now rewrite <- Hq, <- Hq'.
  - replace n with 1 by trivial.
    constructor; auto with zarith.
Qed.

Theorem prime_ge_2 p : prime p ->  2 <= p.
Proof.
  intros (Hp,_); auto with zarith.
Qed.

Definition prime' p := 1<p /\ (forall n, 1<n<p -> ~ (n|p)).

Lemma Z_0_1_more x : 0<=x -> x=0 \/ x=1 \/ 1<x.
Proof.
 intros H. Z.le_elim H; auto.
 apply Z.le_succ_l in H. change (1 <= x) in H. Z.le_elim H; auto.
Qed.

Theorem prime_alt p : prime' p <-> prime p.
Proof.
  split; intros (Hp,H).
  - (* prime -> prime' *)
    constructor; trivial; intros n Hn.
    constructor; auto with zarith; intros x Hxn Hxp.
    rewrite <- Z.divide_abs_l in Hxn, Hxp |- *.
    assert (Hx := Z.abs_nonneg x).
    set (y:=Z.abs x) in *; clearbody y; clear x; rename y into x.
    destruct (Z_0_1_more x Hx) as [->|[->|Hx']].
    + exfalso. apply Z.divide_0_l in Hxn. omega.
    + now exists 1.
    + elim (H x); auto.
      split; trivial.
      apply Z.le_lt_trans with n; auto with zarith.
      apply Z.divide_pos_le; auto with zarith.
  - (* prime' -> prime *)
    constructor; trivial. intros n Hn Hnp.
    case (Zis_gcd_unique n p n 1); auto with zarith.
    constructor; auto with zarith.
    apply H; auto with zarith.
Qed.

Theorem square_not_prime: forall a, ~ prime (a * a).
Proof.
  intros a Ha.
  rewrite <- (Z.abs_square a) in Ha.
  assert (H:=Z.abs_nonneg a).
  set (b:=Z.abs a) in *; clearbody b; clear a; rename b into a.
  rewrite <- prime_alt in Ha; destruct Ha as (Ha,Ha').
  assert (H' : 1 < a) by now apply (Z.square_lt_simpl_nonneg 1).
  apply (Ha' a).
  + split; trivial.
    rewrite <- (Z.mul_1_l a) at 1. apply Z.mul_lt_mono_pos_r; omega.
  + exists a; auto.
Qed.

Theorem prime_div_prime: forall p q,
 prime p -> prime q -> (p | q) -> p = q.
Proof.
  intros p q H H1 H2;
  assert (Hp: 0 < p); try apply Z.lt_le_trans with 2; try apply prime_ge_2; auto with zarith.
  assert (Hq: 0 < q); try apply Z.lt_le_trans with 2; try apply prime_ge_2; auto with zarith.
  case prime_divisors with (2 := H2); auto.
  intros H4; contradict Hp; subst; auto with zarith.
  intros [H4| [H4 | H4]]; subst; auto.
  contradict H; auto; apply not_prime_1.
  contradict Hp; auto with zarith.
Qed.

(** we now prove that [Z.gcd] is indeed a gcd in
   the sense of [Zis_gcd]. *)

Notation Zgcd_is_pos := Z.gcd_nonneg (only parsing).

Lemma Zgcd_is_gcd : forall a b, Zis_gcd a b (Z.gcd a b).
Proof.
 constructor.
 apply Z.gcd_divide_l.
 apply Z.gcd_divide_r.
 apply Z.gcd_greatest.
Qed.

Theorem Zgcd_spec : forall x y : Z, {z : Z | Zis_gcd x y z /\ 0 <= z}.
Proof.
  intros x y; exists (Z.gcd x y).
  split; [apply Zgcd_is_gcd  | apply Z.gcd_nonneg].
Qed.

Theorem Zdivide_Zgcd: forall p q r : Z,
 (p | q) -> (p | r) -> (p | Z.gcd q r).
Proof.
 intros. now apply Z.gcd_greatest.
Qed.

Theorem Zis_gcd_gcd: forall a b c : Z,
 0 <= c ->  Zis_gcd a b c -> Z.gcd a b = c.
Proof.
  intros a b c H1 H2.
  case (Zis_gcd_uniqueness_apart_sign a b c (Z.gcd a b)); auto.
  apply Zgcd_is_gcd; auto.
  Z.le_elim H1.
  - generalize (Z.gcd_nonneg a b); auto with zarith.
  - subst. now case (Z.gcd a b).
Qed.

Notation Zgcd_inv_0_l := Z.gcd_eq_0_l (only parsing).
Notation Zgcd_inv_0_r := Z.gcd_eq_0_r (only parsing).

Theorem Zgcd_div_swap0 : forall a b : Z,
 0 < Z.gcd a b ->
 0 < b ->
 (a / Z.gcd a b) * b = a * (b/Z.gcd a b).
Proof.
  intros a b Hg Hb.
  assert (F := Zgcd_is_gcd a b); inversion F as [F1 F2 F3].
  pattern b at 2; rewrite (Zdivide_Zdiv_eq (Z.gcd a b) b); auto.
  repeat rewrite Z.mul_assoc; f_equal.
  rewrite Z.mul_comm.
  rewrite <- Zdivide_Zdiv_eq; auto.
Qed.

Theorem Zgcd_div_swap : forall a b c : Z,
 0 < Z.gcd a b ->
 0 < b ->
 (c * a) / Z.gcd a b * b = c * a * (b/Z.gcd a b).
Proof.
  intros a b c Hg Hb.
  assert (F := Zgcd_is_gcd a b); inversion F as [F1 F2 F3].
  pattern b at 2; rewrite (Zdivide_Zdiv_eq (Z.gcd a b) b); auto.
  repeat rewrite Z.mul_assoc; f_equal.
  rewrite Zdivide_Zdiv_eq_2; auto.
  repeat rewrite <- Z.mul_assoc; f_equal.
  rewrite Z.mul_comm.
  rewrite <- Zdivide_Zdiv_eq; auto.
Qed.

Notation Zgcd_comm := Z.gcd_comm (compat "8.7").

Lemma Zgcd_ass a b c : Z.gcd (Z.gcd a b) c = Z.gcd a (Z.gcd b c).
Proof.
 symmetry. apply Z.gcd_assoc.
Qed.

Notation Zgcd_Zabs := Z.gcd_abs_l (only parsing).
Notation Zgcd_0 := Z.gcd_0_r (only parsing).
Notation Zgcd_1 := Z.gcd_1_r (only parsing).

Hint Resolve Z.gcd_0_r Z.gcd_1_r : zarith.

Theorem Zgcd_1_rel_prime : forall a b,
 Z.gcd a b = 1 <-> rel_prime a b.
Proof.
  unfold rel_prime; split; intro H.
  rewrite <- H; apply Zgcd_is_gcd.
  case (Zis_gcd_unique a b (Z.gcd a b) 1); auto.
  apply Zgcd_is_gcd.
  intros H2; absurd (0 <= Z.gcd a b); auto with zarith.
  generalize (Z.gcd_nonneg a b); auto with zarith.
Qed.

Definition rel_prime_dec: forall a b,
 { rel_prime a b }+{ ~ rel_prime a b }.
Proof.
  intros a b; case (Z.eq_dec (Z.gcd a b) 1); intros H1.
  left; apply -> Zgcd_1_rel_prime; auto.
  right; contradict H1; apply <- Zgcd_1_rel_prime; auto.
Defined.

Definition prime_dec_aux:
 forall p m,
  { forall n, 1 < n < m -> rel_prime n p } +
  { exists n, 1 < n < m  /\ ~ rel_prime n p }.
Proof.
  intros p m.
  case (Z_lt_dec 1 m); intros H1;
   [ | left; intros; exfalso; omega ].
  pattern m; apply natlike_rec; auto with zarith.
  left; intros; exfalso; omega.
  intros x Hx IH; destruct IH as [F|E].
  destruct (rel_prime_dec x p) as [Y|N].
  left; intros n [HH1 HH2].
  rewrite Z.lt_succ_r in HH2.
  Z.le_elim HH2; subst; auto with zarith.
  - case (Z_lt_dec 1 x); intros HH1.
    * right; exists x; split; auto with zarith.
    * left; intros n [HHH1 HHH2]; contradict HHH1; auto with zarith.
  - right; destruct E as (n,((H0,H2),H3)); exists n; auto with zarith.
Defined.

Definition prime_dec: forall p, { prime p }+{ ~ prime p }.
Proof.
  intros p; case (Z_lt_dec 1 p); intros H1.
  + case (prime_dec_aux p p); intros H2.
    * left; apply prime_intro; auto.
      intros n (Hn1,Hn2). Z.le_elim Hn1; auto; subst n.
      constructor; auto with zarith.
    * right; intros H3; inversion_clear H3 as [Hp1 Hp2].
      case H2; intros n [Hn1 Hn2]; case Hn2; auto with zarith.
  + right; intros H3; inversion_clear H3 as [Hp1 Hp2]; case H1; auto.
Defined.

Theorem not_prime_divide:
 forall p, 1 < p -> ~ prime p -> exists n, 1 < n < p  /\ (n | p).
Proof.
  intros p Hp Hp1.
  case (prime_dec_aux p p); intros H1.
  - elim Hp1; constructor; auto.
    intros n (Hn1,Hn2).
    Z.le_elim Hn1; auto with zarith.
    subst n; constructor; auto with zarith.
  - case H1; intros n (Hn1,Hn2).
    destruct (Z_0_1_more _ (Z.gcd_nonneg n p)) as [H|[H|H]].
    + exfalso. apply Z.gcd_eq_0_l in H. omega.
    + elim Hn2. red. rewrite <- H. apply Zgcd_is_gcd.
    + exists (Z.gcd n p); split; [ split; auto | apply Z.gcd_divide_r ].
      apply Z.le_lt_trans with n; auto with zarith.
      apply Z.divide_pos_le; auto with zarith.
      apply Z.gcd_divide_l.
Qed.
