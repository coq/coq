(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Local Set Warnings "-deprecated".
Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Require Import Zdivisibility.
Require Import Wf_nat.
Require Import Lia Cring Ncring_tac.

Local Set Warnings "-deprecated".

(** For compatibility reasons, this Open Scope isn't local as it should *)

Open Scope Z_scope.

Local Ltac Tauto.intuition_solver ::= auto with zarith.

(** This file contains some notions of number theory upon Z numbers:
     - a divisibility predicate [Z.divide]
     - a gcd predicate [gcd]
     - Euclid algorithm [extgcd]
     - a relatively prime predicate [rel_prime]
     - a prime predicate [prime]
     - properties of the efficient [Z.gcd] function
*)

(** The former specialized inductive predicate [Z.divide] is now
    a generic existential predicate. *)

(** Its former constructor is now a pseudo-constructor. *)

#[deprecated(use=ex_intro, since="9.0")]
Definition Zdivide_intro a b q (H:b=q*a) : Z.divide a b := ex_intro _ q H.

(** Results concerning divisibility*)

#[deprecated(use=Z.divide_1_l, since="9.0")]
Notation Zone_divide := Z.divide_1_l (only parsing).
#[deprecated(use=Z.divide_0_r, since="9.0")]
Notation Zdivide_0 := Z.divide_0_r (only parsing).
#[deprecated(use=Z.mul_divide_mono_l, since="9.0")]
Notation Zmult_divide_compat_l := Z.mul_divide_mono_l (only parsing).
#[deprecated(use=Z.mul_divide_mono_r, since="9.0")]
Notation Zmult_divide_compat_r := Z.mul_divide_mono_r (only parsing).
#[deprecated(use=Z.divide_add_r, since="9.0")]
Notation Zdivide_plus_r := Z.divide_add_r (only parsing).
#[deprecated(use=Z.divide_sub_r, since="9.0")]
Notation Zdivide_minus_l := Z.divide_sub_r (only parsing).
#[deprecated(use=Z.divide_mul_l, since="9.0")]
Notation Zdivide_mult_l := Z.divide_mul_l (only parsing).
#[deprecated(use=Z.divide_mul_r, since="9.0")]
Notation Zdivide_mult_r := Z.divide_mul_r (only parsing).
#[deprecated(use=Z.divide_factor_l, since="9.0")]
Notation Zdivide_factor_r := Z.divide_factor_l (only parsing).
#[deprecated(use=Z.divide_factor_r, since="9.0")]
Notation Zdivide_factor_l := Z.divide_factor_r (only parsing).

#[deprecated(use=Z.divide_opp_r, since="9.0")]
Lemma Zdivide_opp_r a b : (a | b) -> (a | - b).
Proof. apply Z.divide_opp_r. Qed.

#[deprecated(use=Z.divide_opp_r, since="9.0")]
Lemma Zdivide_opp_r_rev a b : (a | - b) -> (a | b).
Proof. apply Z.divide_opp_r. Qed.

#[deprecated(use=Z.divide_opp_l, since="9.0")]
Lemma Zdivide_opp_l a b : (a | b) -> (- a | b).
Proof. apply Z.divide_opp_l. Qed.

#[deprecated(use=Z.divide_opp_l, since="9.0")]
Lemma Zdivide_opp_l_rev a b : (- a | b) -> (a | b).
Proof. apply Z.divide_opp_l. Qed.

#[deprecated(use=Z.divide_abs_l, since="9.0")]
Theorem Zdivide_Zabs_l a b : (Z.abs a | b) -> (a | b).
Proof. apply Z.divide_abs_l. Qed.

#[deprecated(use=Z.divide_abs_l, since="9.0")]
Theorem Zdivide_Zabs_inv_l a b : (a | b) -> (Z.abs a | b).
Proof. apply Z.divide_abs_l. Qed.

#[global]
Hint Resolve Z.divide_refl Z.divide_1_l Z.divide_0_r: zarith.
#[global]
Hint Resolve Z.mul_divide_mono_l Z.mul_divide_mono_r: zarith.
#[global]
Hint Resolve Z.divide_add_r Zdivide_opp_r Zdivide_opp_r_rev Zdivide_opp_l
  Zdivide_opp_l_rev Z.divide_sub_r Z.divide_mul_l Z.divide_mul_r
  Z.divide_factor_l Z.divide_factor_r: zarith.

(** Auxiliary result. *)

#[deprecated(use=Z.eq_mul_1_nonneg, since="9.0")]
Lemma Zmult_one x y : x >= 0 -> x * y = 1 -> x = 1.
Proof.
 Z.swap_greater. apply Z.eq_mul_1_nonneg.
Qed.

(** Only [1] and [-1] divide [1]. *)

#[deprecated(use=Z.divide_1_r, since="9.0")]
Notation Zdivide_1 := Z.divide_1_r (only parsing).

(** If [a] divides [b] and [b<>0] then [|a| <= |b|]. *)

#[deprecated(use=Z.absle_divide, since="9.0")]
Notation Zdivide_bounds := Z.absle_divide (only parsing).

(** [Z.divide] can be expressed using [Z.modulo]. *)

#[deprecated(use=Z.mod0_divide, since="9.0")]
Lemma Zmod_divide : forall a b, b<>0 -> a mod b = 0 -> (b | a).
Proof.
 apply Z.mod_divide.
Qed.

#[deprecated(use=Z.mod0_divide, since="9.0")]
Lemma Zdivide_mod : forall a b, (b | a) -> a mod b = 0.
Proof.
 intros a b (c,->); apply Z_mod_mult.
Qed.

(** [Z.divide] is hence decidable *)
#[deprecated(use=Z.BoolSpec_divide, since="9.0")]
Lemma Zdivide_dec a b : {(a | b)} + {~ (a | b)}.
Proof.
 destruct (Z.eq_dec a 0) as [Ha|Ha].
 - destruct (Z.eq_dec b 0) as [Hb|Hb].
   + left; subst; apply Z.divide_0_r.
   + right. subst. contradict Hb. now apply Z.divide_0_l.
 - destruct (Z.eq_dec (b mod a) 0).
   + left. now apply Z.mod_divide.
   + right. now rewrite <- Z.mod_divide.
Defined.

#[deprecated(use=Z.lt_neq, since="9.0")]
Lemma Z_lt_neq {x y: Z} : x < y -> y <> x.
Proof. auto using Z.lt_neq, Z.neq_sym. Qed.

Theorem Zdivide_Zdiv_eq a b : 0 < a -> (a | b) ->  b = a * (b / a).
Proof.
 intros Ha H.
 rewrite (Z.div_mod b a) at 1.
 + rewrite Zdivide_mod; auto with zarith.
 + auto using Z_lt_neq.
Qed.

Theorem Zdivide_Zdiv_eq_2 a b c :
 0 < a -> (a | b) -> (c * b) / a = c * (b / a).
Proof.
 intros. apply Z.divide_div_mul_exact.
 + now apply Z_lt_neq.
 + auto with zarith.
Qed.

#[deprecated(use=Z.divide_pos_le, since="9.0")]
Theorem Zdivide_le: forall a b : Z,
 0 <= a -> 0 < b -> (a | b) ->  a <= b.
Proof.
 intros. now apply Z.divide_pos_le.
Qed.

Theorem Zdivide_Zdiv_lt_pos a b :
 1 < a -> 0 < b -> (a | b) ->  0 < b / a < b .
Proof.
  intros H1 H2 H3.
  assert (0 < a) by (now transitivity 1).
  split.
  + apply Z.mul_pos_cancel_l with a; auto.
    rewrite <- Zdivide_Zdiv_eq; auto.
  + now apply Z.div_lt.
Qed.

#[deprecated(use=Z.mod_mod_divide, since="9.0")]
Lemma Zmod_div_mod n m a:
 0 < n -> 0 < m -> (n | m) -> a mod n = (a mod m) mod n.
Proof with auto using Z_lt_neq.
  intros H1 H2 (p,Hp).
  rewrite (Z.div_mod a m) at 1...
  rewrite Hp at 1.
  rewrite Z.mul_shuffle0, Z.add_comm, Z.mod_add...
Qed.

Lemma Zmod_divide_minus a b c:
 0 < b -> a mod b = c -> (b | a - c).
Proof with auto using Z_lt_neq.
  intros H H1. apply Z.mod_divide...
  rewrite Zminus_mod.
  rewrite H1. rewrite <- (Z.mod_small c b) at 1.
  - rewrite Z.sub_diag, Z.mod_0_l...
  - subst. now apply Z.mod_pos_bound.
Qed.

Lemma Zdivide_mod_minus a b c:
 0 <= c < b -> (b | a - c) -> a mod b = c.
Proof.
  intros (H1, H2) H3.
  assert (0 < b) by Z.order.
  assert (b <> 0) by now apply Z_lt_neq.
  replace a with ((a - c) + c) by ring.
  rewrite Z.add_mod; auto.
  rewrite (Zdivide_mod (a-c) b); try rewrite Z.add_0_l; auto.
  rewrite Z.mod_mod; try apply Zmod_small; auto.
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

#[deprecated(use=Z.gcd, since="9.0")]
Lemma Zgcd_is_gcd : forall a b, Zis_gcd a b (Z.gcd a b).
Proof.
 constructor.
 - apply Z.gcd_divide_l.
 - apply Z.gcd_divide_r.
 - apply Z.gcd_greatest.
Qed.

(** Trivial properties of [gcd] *)

Lemma Zis_gcd_sym : forall a b d, Zis_gcd a b d -> Zis_gcd b a d.
Proof.
  induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_0 : forall a, Zis_gcd a 0 a.
Proof.
  constructor; auto with zarith.
Qed.

#[deprecated(use=Z.gcd_1_r, since="9.0")]
Lemma Zis_gcd_1 : forall a, Zis_gcd a 1 1.
Proof.
  constructor; auto with zarith.
Qed.

#[deprecated(use=Z.gcd_diag, since="9.0")]
Lemma Zis_gcd_refl : forall a, Zis_gcd a a a.
Proof.
  constructor; auto with zarith.
Qed.

Lemma Zis_gcd_minus : forall a b d, Zis_gcd a (- b) d -> Zis_gcd b a d.
Proof.
  induction 1; constructor; intuition.
Qed.

#[deprecated(note="Z.cd is always non-negative", since="9.0")]
Lemma Zis_gcd_opp : forall a b d, Zis_gcd a b d -> Zis_gcd b a (- d).
Proof.
  induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_0_abs a : Zis_gcd 0 a (Z.abs a).
Proof.
  apply Zabs_ind.
  - intros; apply Zis_gcd_sym; apply Zis_gcd_0; auto.
  - intros; apply Zis_gcd_opp; apply Zis_gcd_0; auto.
Qed.

#[global]
Hint Resolve Zis_gcd_sym Zis_gcd_0 Zis_gcd_minus Zis_gcd_opp: zarith.

#[deprecated(use=f_equal, note="Use Z.gcd", since="9.0")]
Theorem Zis_gcd_unique: forall a b c d : Z,
 Zis_gcd a b c -> Zis_gcd a b d ->  c = d \/ c = (- d).
Proof.
intros a b c d [Hc1 Hc2 Hc3] [Hd1 Hd2 Hd3].
assert (c|d) by auto.
assert (d|c) by auto.
apply Z.divide_antisym; auto.
Qed.


(** * Extended Euclid algorithm. *)

Lemma deprecated_Zis_gcd_for_euclid :
  forall a b d q:Z, Zis_gcd b (a - q * b) d -> Zis_gcd a b d.
Proof.
  intros a b d q; simple induction 1; constructor; intuition.
  replace a with (a - q * b + q * b).
  - auto with zarith.
  - ring.
Qed.
#[deprecated(since="8.17")]
Notation Zis_gcd_for_euclid := deprecated_Zis_gcd_for_euclid (only parsing).

(* this lemma is still used below and in Zgcd_alt *)
#[deprecated(since="9.0")]
Lemma Zis_gcd_for_euclid2 :
  forall b d q r:Z, Zis_gcd r b d -> Zis_gcd b (b * q + r) d.
Proof.
  intros b d q r; destruct 1 as [? ? H]; constructor; intuition.
  apply H; auto.
  replace r with (b * q + r - b * q).
  - auto with zarith.
  - ring.
Qed.

#[deprecated(use=Z.extgcd, since="9.0")]
Notation extgcd := Z.extgcd (only parsing).

#[deprecated(use=Z.extgcd_correct, since="9.0")]
Notation extgcd_correct := Z.extgcd_correct (only parsing).

Section extended_euclid_algorithm.

  Variables a b : Z.

  Inductive deprecated_Euclid : Set :=
    deprecated_Euclid_intro :
    forall u v d:Z, u * a + v * b = d -> Zis_gcd a b d -> deprecated_Euclid.

  Lemma deprecated_euclid : deprecated_Euclid.
  Proof. case (extgcd a b) as [[]?] eqn:H; case (Z.extgcd_correct a b H); esplit; subst; eauto using Zgcd_is_gcd. Qed.

  Lemma deprecated_euclid_rec :
    forall v3:Z,
      0 <= v3 ->
      forall u1 u2 u3 v1 v2:Z,
       u1 * a + u2 * b = u3 ->
       v1 * a + v2 * b = v3 ->
       (forall d:Z, Zis_gcd u3 v3 d -> Zis_gcd a b d) -> deprecated_Euclid.
  Proof. intros; apply deprecated_euclid. Qed.

End extended_euclid_algorithm.

#[deprecated(since="8.17", note="Use Coq.ZArith.Znumtheory.extgcd")]
Notation Euclid := deprecated_Euclid (only parsing).
#[deprecated(since="8.17", note="Use Coq.ZArith.Znumtheory.extgcd")]
Notation Euclid_intro := deprecated_Euclid_intro (only parsing).
#[deprecated(since="8.17", note="Use Coq.ZArith.Znumtheory.extgcd")]
Notation euclid := deprecated_euclid (only parsing).
#[deprecated(since="8.17", note="Use Coq.ZArith.Znumtheory.extgcd")]
Notation euclid_rec := deprecated_euclid_rec (only parsing).

#[deprecated(use=Z.gcd_unique, since="9.0")]
Theorem Zis_gcd_uniqueness_apart_sign :
  forall a b d d':Z, Zis_gcd a b d -> Zis_gcd a b d' -> d = d' \/ d = - d'.
Proof.
  intros a b d d'; simple induction 1.
  intros H1 H2 H3; destruct 1 as [H4 H5 H6].
  generalize (H3 d' H4 H5); intro Hd'd.
  generalize (H6 d H1 H2); intro Hdd'.
  exact (Z.divide_antisym d d' Hdd' Hd'd).
Qed.

(** * Bezout's coefficients *)

Inductive Bezout_deprecated (a b d:Z) : Prop :=
  Bezout_deprecated_intro : forall u v:Z, u * a + v * b = d -> Bezout_deprecated a b d.

#[deprecated(use=Z.Bezout, since="9.0")]
Notation Bezout := Bezout_deprecated (only parsing).
#[deprecated(use=ex_intro, since="9.0")]
Notation Bezout_intro := Bezout_deprecated_intro (only parsing).

(** Existence of Bezout's coefficients for the [gcd] of [a] and [b] *)
#[deprecated(use=Z.Bezout_coprime_iff, since="9.0")]
Lemma Zis_gcd_bezout : forall a b d:Z, Zis_gcd a b d -> Bezout a b d.
Proof.
  intros a b d Hgcd.
  case (extgcd a b) as [[u v] g] eqn:E, (extgcd_correct _ _ E) as [G ?Hg].
  destruct (Zis_gcd_uniqueness_apart_sign a b d g Hgcd ltac:(rewrite Hg; apply Zgcd_is_gcd));
    subst; (apply Bezout_intro with u v + apply Bezout_intro with (- u) (- v)); ring.
Qed.

(** gcd of [ca] and [cb] is [c gcd(a,b)]. *)

#[deprecated(use=Z.gcd_mul_mono_l, since="9.0")]
Lemma Zis_gcd_mult :
  forall a b c d:Z, Zis_gcd a b d -> Zis_gcd (c * a) (c * b) (c * d).
Proof.
  intros a b c d; intro H; generalize H; simple induction 1. constructor; auto with zarith.
  intros x Ha Hb.
  elim (Zis_gcd_bezout a b d H). intros u v Huv.
  elim Ha; intros a' Ha'.
  elim Hb; intros b' Hb'.
  apply Zdivide_intro with (u * a' + v * b').
  rewrite <- Huv.
  replace (c * (u * a + v * b)) with (u * (c * a) + v * (c * b)).
  - rewrite Ha'; rewrite Hb'; ring.
  - ring.
Qed.


(** * Relative primality *)

Definition rel_prime (a b:Z) : Prop := Zis_gcd a b 1.

Lemma rel_prime_iff_coprime  a b : rel_prime a b <-> Z.coprime a b.
Proof.
  symmetry; unfold rel_prime; split; intros H.
  - rewrite <- H; apply Zgcd_is_gcd.
  - case (Zis_gcd_unique a b (Z.gcd a b) 1); auto.
    + apply Zgcd_is_gcd.
    + intros H2; absurd (0 <= Z.gcd a b); auto with zarith.
      * rewrite H2; red; auto.
      * generalize (Z.gcd_nonneg a b); auto with zarith.
Qed.

(** Bezout's theorem: [a] and [b] are relatively prime if and
    only if there exist [u] and [v] such that [ua+vb = 1]. *)

#[deprecated(use=Z.Bezout_coprime, since="9.0")]
Lemma rel_prime_bezout : forall a b:Z, rel_prime a b -> Bezout a b 1.
Proof.
  intros a b; exact (Zis_gcd_bezout a b 1).
Qed.

#[deprecated(use=Z.coprime_Bezout, since="9.0")]
Lemma bezout_rel_prime : forall a b:Z, Bezout a b 1 -> rel_prime a b.
Proof.
  simple induction 1; intros ? ? H0; constructor; auto with zarith.
  intros. rewrite <- H0; auto with zarith.
Qed.

(** Gauss's theorem: if [a] divides [bc] and if [a] and [b] are
    relatively prime, then [a] divides [c]. *)

#[deprecated(use=Z.gauss, since="9.0")]
Theorem Gauss : forall a b c:Z, (a | b * c) -> rel_prime a b -> (a | c).
Proof.
  intros a b c H H0. elim (rel_prime_bezout a b H0); intros u v H1.
  replace c with (c * 1); [ idtac | ring ].
  rewrite <- H1.
  replace (c * (u * a + v * b)) with (c * u * a + v * (b * c));
    [ eauto with zarith | ring ].
Qed.

(** If [a] is relatively prime to [b] and [c], then it is to [bc] *)

#[deprecated(use=Z.coprime_mul_r, since="9.0")]
Lemma rel_prime_mult :
  forall a b c:Z, rel_prime a b -> rel_prime a c -> rel_prime a (b * c).
Proof. setoid_rewrite rel_prime_iff_coprime; apply Z.coprime_mul_r. Qed.

#[deprecated(note="Consider Z.gcd instead", since="9.0")]
Lemma rel_prime_cross_prod :
  forall a b c d:Z,
    rel_prime a b ->
    rel_prime c d -> b > 0 -> d > 0 -> a * d = b * c -> a = c /\ b = d.
Proof.
  intros a b c d; intros H H0 H1 H2 H3.
  elim (Z.divide_antisym b d).
  - intros H4; split; auto with zarith.
    rewrite H4 in H3.
    rewrite Z.mul_comm in H3.
    apply Z.mul_reg_l with d; auto.
    contradict H2; rewrite H2; discriminate.
  - intros H4; contradict H1; rewrite H4.
    apply Zgt_asym, Z.lt_gt, Z.opp_lt_mono.
    now rewrite Z.opp_involutive; apply Z.gt_lt.
  - apply Gauss with a.
    + rewrite H3; auto with zarith.
    + now apply Zis_gcd_sym.
  - apply Gauss with c.
    + rewrite Z.mul_comm.
      rewrite <- H3.
      auto with zarith.
    + now apply Zis_gcd_sym.
Qed.

(** After factorization by a gcd, the original numbers are relatively prime. *)

#[deprecated(use=Z.gcd_div_gcd, since="9.0")]
Lemma Zis_gcd_rel_prime :
  forall a b g:Z,
    b > 0 -> g >= 0 -> Zis_gcd a b g -> rel_prime (a / g) (b / g).
Proof.
  intros a b g; intros H H0 H1.
  assert (H2 : g <> 0) by
    (intro H2;
    elim H1; intros ? H4 ?;
    elim H4; intros ? H6;
    rewrite H2 in H6; subst b;
    contradict H; rewrite Z.mul_0_r; discriminate).
  assert (H3 : g > 0) by
    (apply Z.lt_gt, Z.le_neq; split; try apply Z.ge_le; auto).
  unfold rel_prime.
  destruct H1 as [Ha  Hb Hab].
  destruct Ha as [a' Ha'].
  destruct Hb as [b' Hb'].
  replace (a/g) with a';
    [|rewrite Ha'; rewrite Z_div_mult; auto with zarith].
  replace (b/g) with b';
      [|rewrite Hb'; rewrite Z_div_mult; auto with zarith].
  constructor.
  - exists a'; rewrite ?Z.mul_1_r; auto with zarith.
  - exists b'; rewrite ?Z.mul_1_r; auto with zarith.
  - intros x (xa,H5) (xb,H6).
    destruct (Hab (x*g)) as (x',Hx').
    + exists xa; rewrite Z.mul_assoc; rewrite <- H5; auto.
    + exists xb; rewrite Z.mul_assoc; rewrite <- H6; auto.
    + replace g with (1*g) in Hx'; auto with zarith.
      do 2 rewrite Z.mul_assoc in Hx'.
      apply Z.mul_reg_r in Hx'; trivial.
      rewrite Z.mul_1_r in Hx'.
      exists x'; auto with zarith.
Qed.

#[deprecated(use=Z.Symmetric_coprime, since="9.0")]
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

#[deprecated(use=Z.coprime_1_l, since="9.0")]
Theorem rel_prime_1: forall n, rel_prime 1 n.
Proof.
  intros n; red; apply Zis_gcd_intro; auto.
  - exists 1; reflexivity.
  - exists n; rewrite Z.mul_1_r; reflexivity.
Qed.

#[deprecated(use=Z.coprime_0_l_iff, since="9.0")]
Theorem not_rel_prime_0: forall n, 1 < n -> ~ rel_prime 0 n.
Proof.
  intros n H H1; absurd (n = 1 \/ n = -1).
  - intros [H2 | H2]; subst; contradict H; discriminate.
  - case (Zis_gcd_unique  0 n n 1); auto.
    apply Zis_gcd_intro; auto.
    + exists 0; reflexivity.
    + exists 1; rewrite Z.mul_1_l; reflexivity.
Qed.

#[deprecated(use=Z.coprime_mod_l_iff, since="9.0")]
Theorem rel_prime_mod: forall p q, 0 < q ->
 rel_prime p q -> rel_prime (p mod q) q.
Proof.
  intros p q H H0.
  assert (H1: Bezout p q 1).
  - apply rel_prime_bezout; auto.
  - inversion_clear H1 as [q1 r1 H2].
    apply bezout_rel_prime.
    apply Bezout_intro with q1  (r1 + q1 * (p / q)).
    rewrite <- H2.
    pattern p at 3; rewrite (Z_div_mod_eq_full p q); ring.
Qed.

#[deprecated(use=Z.coprime_mod_l_iff, since="9.0")]
Theorem rel_prime_mod_rev: forall p q, 0 < q ->
 rel_prime (p mod q) q -> rel_prime p q.
Proof.
  intros p q H H0.
  rewrite (Z_div_mod_eq_full p q). red.
  apply Zis_gcd_sym; apply Zis_gcd_for_euclid2; auto.
Qed.

#[deprecated(note="unfold Z.coprime", since="9.0")]
Theorem Zrel_prime_neq_mod_0: forall a b, 1 < b -> rel_prime a b -> a mod b <> 0.
Proof.
  intros a b H H1 H2.
  case (not_rel_prime_0 _ H).
  rewrite <- H2.
  apply rel_prime_mod; auto.
  now transitivity 1.
Qed.

(** * Primality *)

(** Note: prefer Z.prime *)
Inductive prime (p:Z) : Prop :=
  prime_intro :
    1 < p -> (forall n:Z, 1 <= n < p -> rel_prime n p) -> prime p.

(** The sole divisors of a prime number [p] are [-1], [1], [p] and [-p]. *)

Lemma prime_divisors :
  forall p:Z,
    prime p -> forall a:Z, (a | p) -> a = -1 \/ a = 1 \/ a = p \/ a = - p.
Proof.
  intros p; destruct 1 as [H H0]; intros a ?.
  assert
    (a = - p \/ - p < a < -1 \/ a = -1 \/ a = 0 \/ a = 1 \/ 1 < a < p \/ a = p).
  { assert (Z.abs a <= Z.abs p) as H2 by
        (apply Zdivide_bounds; [ assumption | now intros -> ]).
    revert H2.
    pattern (Z.abs a); apply Zabs_ind; pattern (Z.abs p); apply Zabs_ind;
    intros H2 H3 H4.
    - destruct (Zle_lt_or_eq _ _ H4) as [H5 | H5]; try intuition.
      destruct (Zle_lt_or_eq _ _ (Z.ge_le _ _ H3)) as [H6 | H6]; try intuition.
      destruct (Zle_lt_or_eq _ _ (Zlt_le_succ _ _ H6)) as [H7 | H7]; intuition.
    - contradict H2; apply Zlt_not_le; apply Z.lt_trans with (2 := H); red; auto.
    - destruct (Zle_lt_or_eq _ _ H4) as [H5 | H5].
      + destruct (Zle_lt_or_eq _ _  H3) as [H6 | H6]; try intuition.
        assert (H7 : a <= Z.pred 0) by (apply Z.lt_le_pred; auto).
        destruct (Zle_lt_or_eq _ _ H7) as [H8 | H8]; intuition.
        assert (- p < a < -1); try intuition.
        now apply Z.opp_lt_mono; rewrite Z.opp_involutive.
      + now left; rewrite <- H5, Z.opp_involutive.
    - contradict H2.
      apply Zlt_not_le; apply Z.lt_trans with (2 := H); red; auto.
    }
  intuition idtac.
  (* -p < a < -1 *)
  - match goal with [hyp : a < -1 |- _] => rename hyp into H4 end.
    absurd (rel_prime (- a) p).
    + intros [H1p H2p H3p].
      assert (- a | - a) by auto with zarith.
      assert (- a | p) as H5 by auto with zarith.
      apply H3p, Z.divide_1_r in H5; auto with zarith.
      destruct H5 as [H5|H5].
      * contradict H4; rewrite <- (Z.opp_involutive a), H5 .
        apply Z.lt_irrefl.
      * contradict H4; rewrite <- (Z.opp_involutive a), H5 .
        discriminate.
    + apply H0; split.
      * now apply Z.opp_le_mono; rewrite Z.opp_involutive; apply Z.lt_le_incl.
      * now apply Z.opp_lt_mono; rewrite Z.opp_involutive.
  (* a = 0 *)
  - match goal with [hyp : a = 0 |- _] => rename hyp into H2 end.
    contradict H.
    replace p with 0; try discriminate.
    now apply sym_equal, Z.divide_0_l; rewrite <-H2.
  (* 1 < a < p *)
  - match goal with [hyp : 1 < a |- _] => rename hyp into H3 end.
    absurd (rel_prime a p).
    + intros [H1p H2p H3p].
      assert (a | a) by auto with zarith.
      assert (a | p) as H5 by auto with zarith.
      apply H3p, Z.divide_1_r in H5; auto with zarith.
      destruct H5 as [H5|H5].
      * contradict H3; rewrite <- (Z.opp_involutive a), H5 .
        apply Z.lt_irrefl.
      * contradict H3; rewrite <- (Z.opp_involutive a), H5 .
        discriminate.
    + apply H0; split; auto.
      now apply Z.lt_le_incl.
Qed.

(** A prime number is relatively prime with any number it does not divide *)

Lemma prime_rel_prime :
  forall p:Z, prime p -> forall a:Z, ~ (p | a) -> rel_prime p a.
Proof.
  intros p H a H0; constructor; auto with zarith; intros ? H1 H2.
  apply prime_divisors in H1; intuition; subst; auto with zarith.
  - absurd (p | a); auto with zarith.
  - absurd (p | a); intuition.
Qed.

#[global]
Hint Resolve prime_rel_prime: zarith.

(** As a consequence, a prime number is relatively prime with smaller numbers *)

Theorem rel_prime_le_prime:
 forall a p, prime p -> 1 <=  a < p -> rel_prime a p.
Proof.
  intros a p Hp [H1 H2].
  apply rel_prime_sym; apply prime_rel_prime; auto.
  intros [q Hq]; subst a.
  destruct Hp as [H3 H4].
  contradict H2; apply Zle_not_lt.
  rewrite <- (Z.mul_1_l p) at 1.
  apply Zmult_le_compat_r.
  - apply (Zlt_le_succ 0).
    apply Zmult_lt_0_reg_r with p.
    + apply Z.le_succ_l, Z.lt_le_incl; auto.
    + now apply Z.le_succ_l.
  - apply Z.lt_le_incl, Z.le_succ_l, Z.lt_le_incl; auto.
Qed.

(** If a prime [p] divides [ab] then it divides either [a] or [b] *)

Lemma prime_mult :
  forall p:Z, prime p -> forall a b:Z, (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intro p; simple induction 1; intros ? ? a b ?.
  case (Zdivide_dec p a); intuition.
  right; apply Gauss with a; auto with zarith.
Qed.

#[deprecated(use=Z.not_prime_0, since="9.0")]
Lemma not_prime_0: ~ prime 0.
Proof.
  intros H1; case (prime_divisors _ H1 2); auto with zarith; intuition; discriminate.
Qed.

#[deprecated(use=Z.not_prime_1, since="9.0")]
Lemma not_prime_1: ~ prime 1.
Proof.
  intros H1; absurd (1 < 1).
  - discriminate.
  - inversion H1; auto.
Qed.

Lemma prime_2: prime 2.
Proof.
  apply prime_intro.
  - red; auto.
  - intros n (H,H'); Z.le_elim H; auto with zarith.
    + contradict H'; auto with zarith.
      now apply Zle_not_lt, (Zlt_le_succ 1).
    + subst n. constructor; auto with zarith.
Qed.

#[deprecated(use=Z.prime_3, since="9.0")]
Theorem prime_3: prime 3.
Proof.
  apply prime_intro; auto with zarith.
  - red; auto.
  - intros n (H,H'); Z.le_elim H; auto with zarith.
    + replace n with 2.
      * constructor; auto with zarith.
        intros x (q,Hq) (q',Hq').
        exists (q' - q). ring_simplify. now rewrite <- Hq, <- Hq'.
      * apply Z.le_antisymm.
        ++ now apply (Zlt_le_succ 1).
        ++ now apply (Z.lt_le_pred _ 3).
     + replace n with 1 by trivial.
       constructor; auto with zarith.
Qed.

Theorem prime_ge_2 p : prime p ->  2 <= p.
Proof.
  now intros (Hp,_); apply (Zlt_le_succ 1).
Qed.

#[deprecated(use=Z.prime, since="9.0")]
Notation prime' := Z.prime (only parsing).

#[deprecated(note="Use lia", since="9.0")]
Lemma Z_0_1_more x : 0<=x -> x=0 \/ x=1 \/ 1<x.
Proof.
 intros H. Z.le_elim H; auto.
 apply Z.le_succ_l in H. change (1 <= x) in H. Z.le_elim H; auto.
Qed.

Theorem prime_alt p : Z.prime p <-> prime p.
Proof.
  split; intros (Hp,H).
  - (* prime -> prime' *)
    constructor; trivial; intros n Hn.
    constructor; auto with zarith; intros x Hxn Hxp.
    rewrite <- Z.divide_abs_l in Hxn, Hxp |- *.
    assert (Hx := Z.abs_nonneg x).
    set (y:=Z.abs x) in *; clearbody y; clear x; rename y into x.
    destruct (Z_0_1_more x Hx) as [->|[->|Hx']].
    + exfalso. apply Z.divide_0_l in Hxn.
      absurd (1 <= n).
      * rewrite Hxn; red; auto.
      * intuition.
    + now exists 1.
    + elim (H x); auto.
      split; trivial.
      apply Z.le_lt_trans with n; try tauto.
      apply Z.divide_pos_le; auto with zarith.
      apply Z.lt_le_trans with (2 := proj1 Hn); red; auto.
  - (* prime' -> prime *)
    constructor; trivial. intros n Hn Hnp.
    case (Zis_gcd_unique n p n 1).
    + constructor; auto with zarith.
    + apply H; auto with zarith.
      now intuition; apply Z.lt_le_incl.
    + intros H1; intuition; subst n; discriminate.
    + intros H1; intuition; subst n; discriminate.
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
    rewrite <- (Z.mul_1_l a) at 1.
    apply Z.mul_lt_mono_pos_r; auto.
    apply Z.lt_trans with (2 := H'); red; auto.
  + exists a; auto.
Qed.

Theorem prime_div_prime: forall p q,
 prime p -> prime q -> (p | q) -> p = q.
Proof.
  intros p q H H1 H2;
  assert (Hp: 0 < p); try apply Z.lt_le_trans with 2; try apply prime_ge_2; auto with zarith.
  assert (Hq: 0 < q); try apply Z.lt_le_trans with 2; try apply prime_ge_2; auto with zarith.
  case prime_divisors with (2 := H2); auto.
  - intros H4; contradict Hp; subst; discriminate.
  - intros [H4| [H4 | H4]]; subst; auto.
    + contradict H; auto; apply not_prime_1.
    + contradict Hp; apply Zle_not_lt, (Z.opp_le_mono _ 0).
      now rewrite Z.opp_involutive; apply Z.lt_le_incl.
Qed.

#[deprecated(use=Z.gcd_nonneg , since="9.0")]
Notation Zgcd_is_pos := Z.gcd_nonneg (only parsing).

#[deprecated(since="9.0")]
Theorem Zgcd_spec : forall x y : Z, {z : Z | Zis_gcd x y z /\ 0 <= z}.
Proof.
  intros x y; exists (Z.gcd x y).
  split; [apply Zgcd_is_gcd  | apply Z.gcd_nonneg].
Qed.

#[deprecated(use=Z.gcd_greatest, since="9.0")]
Theorem Zdivide_Zgcd: forall p q r : Z,
 (p | q) -> (p | r) -> (p | Z.gcd q r).
Proof.
 intros. now apply Z.gcd_greatest.
Qed.

#[deprecated(use=Z.gcd, since="9.0")]
Theorem Zis_gcd_gcd: forall a b c : Z,
 0 <= c ->  Zis_gcd a b c -> Z.gcd a b = c.
Proof.
  intros a b c H1 H2.
  case (Zis_gcd_uniqueness_apart_sign a b c (Z.gcd a b)); auto.
  - apply Zgcd_is_gcd; auto.
  - Z.le_elim H1.
    + generalize (Z.gcd_nonneg a b); auto with zarith.
      intros H3 H4; contradict H3.
      rewrite <- (Z.opp_involutive (Z.gcd a b)), <- H4.
      now apply Zlt_not_le, Z.opp_lt_mono; rewrite Z.opp_involutive.
    + subst. now case (Z.gcd a b).
Qed.

#[deprecated(use=Z.gcd_eq_0_l , since="9.0")]
Notation Zgcd_inv_0_l := Z.gcd_eq_0_l (only parsing).
#[deprecated(use=Z.gcd_eq_0_r , since="9.0")]
Notation Zgcd_inv_0_r := Z.gcd_eq_0_r (only parsing).

#[deprecated(use=Z.gcd_div_swap, since="9.0")]
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

#[deprecated(use=Z.gcd_div_swap, since="9.0")]
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

#[deprecated(use=Z.gcd_assoc, since="9.0")]
Lemma Zgcd_ass a b c : Z.gcd (Z.gcd a b) c = Z.gcd a (Z.gcd b c).
Proof.
 symmetry. apply Z.gcd_assoc.
Qed.

#[deprecated(use=Z.gcd_abs_l, since="9.0")]
Notation Zgcd_Zabs := Z.gcd_abs_l (only parsing).
#[deprecated(use=Z.gcd_0_r, since="9.0")]
Notation Zgcd_0 := Z.gcd_0_r (only parsing).
#[deprecated(use=Z.gcd_1_r, since="9.0")]
Notation Zgcd_1 := Z.gcd_1_r (only parsing).

#[global]
Hint Resolve Z.gcd_0_r Z.gcd_1_r : zarith.

#[deprecated(note="Use Z.gcd_greatest, Z.gcd_divide_l, or Z.gcd_divide_r", since="9.0")]
Theorem Zgcd_1_rel_prime : forall a b,
 Z.gcd a b = 1 <-> rel_prime a b.
Proof.
  unfold rel_prime; intros a b; split; intro H.
  - rewrite <- H; apply Zgcd_is_gcd.
  - case (Zis_gcd_unique a b (Z.gcd a b) 1); auto.
    + apply Zgcd_is_gcd.
    + intros H2; absurd (0 <= Z.gcd a b); auto with zarith.
      * rewrite H2; red; auto.
      * generalize (Z.gcd_nonneg a b); auto with zarith.
Qed.

#[deprecated(use=Z.BoolSpec_coprime, since="9.0")]
Definition rel_prime_dec: forall a b,
 { rel_prime a b }+{ ~ rel_prime a b }.
Proof.
  intros a b; case (Z.eq_dec (Z.gcd a b) 1); intros H1.
  - left; apply -> Zgcd_1_rel_prime; auto.
  - right; contradict H1; apply <- Zgcd_1_rel_prime; auto.
Defined.

#[deprecated(since="9.0")]
Definition prime_dec_aux:
 forall p m,
  { forall n, 1 < n < m -> rel_prime n p } +
  { exists n, 1 < n < m  /\ ~ rel_prime n p }.
Proof.
  intros p m.
  case (Z_lt_dec 1 m); intros H1;
   [ | left; intros n ?; exfalso;
       contradict H1; apply Z.lt_trans with n; intuition].
  pattern m; apply natlike_rec; auto with zarith.
  - left; intros n ?; exfalso.
    absurd (1 < 0); try discriminate.
    apply Z.lt_trans with  n; intuition.
  - intros x Hx IH; destruct IH as [F|E].
    + destruct (rel_prime_dec x p) as [Y|N].
      * left; intros n [HH1 HH2].
        rewrite Z.lt_succ_r in HH2.
        Z.le_elim HH2; subst; auto with zarith.
      * case (Z_lt_dec 1 x); intros HH1.
        -- right; exists x; split; auto with zarith.
        -- left; intros n [HHH1 HHH2]; contradict HHH1; auto with zarith.
           apply Zle_not_lt; apply Z.le_trans with x.
           ++ now apply Zlt_succ_le.
           ++ now apply Znot_gt_le; contradict HH1; apply Z.gt_lt.
     + right; destruct E as (n,((H0,H2),H3)); exists n; auto with zarith.
  - apply Z.le_trans with (2 := Z.lt_le_incl _ _ H1); discriminate.
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
      now apply Hp2; intuition; apply Z.lt_le_incl.
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
    + exfalso. apply Z.gcd_eq_0_l in H.
      absurd (1 < n).
      * rewrite H; discriminate.
      * now intuition.
    + elim Hn2. red. rewrite <- H. apply Zgcd_is_gcd.
    + exists (Z.gcd n p); split; [ split; auto | apply Z.gcd_divide_r ].
      apply Z.le_lt_trans with n; auto with zarith.
      * apply Z.divide_pos_le; auto with zarith.
        -- apply Z.lt_trans with 1; intuition.
        -- apply Z.gcd_divide_l.
      * intuition.
Qed.
