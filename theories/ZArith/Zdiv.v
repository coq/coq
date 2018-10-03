(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Euclidean Division *)

(** Initial Contribution by Claude Marché and Xavier Urbain *)

Require Export ZArith_base.
Require Import Zbool Omega ZArithRing Zcomplements Setoid Morphisms.
Local Open Scope Z_scope.

(** The definition of the division is now in [BinIntDef], the initial
    specifications and properties are in [BinInt]. *)

Notation Zdiv_eucl_POS := Z.pos_div_eucl (only parsing).
Notation Zdiv_eucl := Z.div_eucl (compat "8.7").
Notation Zdiv := Z.div (compat "8.7").
Notation Zmod := Z.modulo (only parsing).

Notation Zdiv_eucl_eq := Z.div_eucl_eq (compat "8.7").
Notation Z_div_mod_eq_full := Z.div_mod (only parsing).
Notation Zmod_POS_bound := Z.pos_div_eucl_bound (only parsing).
Notation Zmod_pos_bound := Z.mod_pos_bound (only parsing).
Notation Zmod_neg_bound := Z.mod_neg_bound (only parsing).

(** * Main division theorems *)

(** NB: many things are stated twice for compatibility reasons *)

Lemma Z_div_mod_POS :
  forall b:Z,
    b > 0 ->
    forall a:positive,
      let (q, r) := Z.pos_div_eucl a b in Zpos a = b * q + r /\ 0 <= r < b.
Proof.
 intros b Hb a. Z.swap_greater.
 generalize (Z.pos_div_eucl_eq a b Hb) (Z.pos_div_eucl_bound a b Hb).
 destruct Z.pos_div_eucl. rewrite Z.mul_comm. auto.
Qed.

Theorem Z_div_mod a b :
  b > 0 ->
  let (q, r) := Z.div_eucl a b in a = b * q + r /\ 0 <= r < b.
Proof.
 Z.swap_greater. intros Hb.
 assert (Hb' : b<>0) by (now destruct b).
 generalize (Z.div_eucl_eq a b Hb') (Z.mod_pos_bound a b Hb).
 unfold Z.modulo. destruct Z.div_eucl. auto.
Qed.

(** For stating the fully general result, let's give a short name
    to the condition on the remainder. *)

Definition Remainder r b :=  0 <= r < b \/ b < r <= 0.

(** Another equivalent formulation: *)

Definition Remainder_alt r b :=  Z.abs r < Z.abs b /\ Z.sgn r <> - Z.sgn b.

(* In the last formulation, [ Z.sgn r <> - Z.sgn b ] is less nice than saying
    [ Z.sgn r = Z.sgn b ], but at least it works even when [r] is null. *)

Lemma Remainder_equiv : forall r b, Remainder r b <-> Remainder_alt r b.
Proof.
 intros; unfold Remainder, Remainder_alt; omega with *.
Qed.

Hint Unfold Remainder.

(** Now comes the fully general result about Euclidean division. *)

Theorem Z_div_mod_full a b :
  b <> 0 ->
  let (q, r) := Z.div_eucl a b in a = b * q + r /\ Remainder r b.
Proof.
 intros Hb.
 generalize (Z.div_eucl_eq a b Hb)
  (Z.mod_pos_bound a b) (Z.mod_neg_bound a b).
 unfold Z.modulo. destruct Z.div_eucl as (q,r).
 intros EQ POS NEG.
 split; auto.
 red; destruct b.
  now destruct Hb. left; now apply POS. right; now apply NEG.
Qed.

(** The same results as before, stated separately in terms of Z.div and Z.modulo *)

Lemma Z_mod_remainder a b : b<>0 -> Remainder (a mod b) b.
Proof.
  unfold Z.modulo; intros Hb; generalize (Z_div_mod_full a b Hb); auto.
  destruct Z.div_eucl; tauto.
Qed.

Lemma Z_mod_lt a b : b > 0 -> 0 <= a mod b < b.
Proof (fun Hb => Z.mod_pos_bound a b (Z.gt_lt _ _ Hb)).

Lemma Z_mod_neg a b : b < 0 -> b < a mod b <= 0.
Proof (Z.mod_neg_bound a b).

Lemma Z_div_mod_eq a b : b > 0 -> a = b*(a/b) + (a mod b).
Proof.
  intros Hb; apply Z.div_mod; auto with zarith.
Qed.

Lemma Zmod_eq_full a b : b<>0 -> a mod b = a - (a/b)*b.
Proof. intros. rewrite Z.mul_comm. now apply Z.mod_eq. Qed.

Lemma Zmod_eq a b : b>0 -> a mod b = a - (a/b)*b.
Proof. intros. apply Zmod_eq_full. now destruct b. Qed.

(** Existence theorem *)

Theorem Zdiv_eucl_exist : forall (b:Z)(Hb:b>0)(a:Z),
 {qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < b}.
Proof.
  intros b Hb a.
  exists (Z.div_eucl a b).
  exact (Z_div_mod a b Hb).
Qed.

Arguments Zdiv_eucl_exist : default implicits.


(** Uniqueness theorems *)

Theorem Zdiv_mod_unique b q1 q2 r1 r2 :
  0 <= r1 < Z.abs b -> 0 <= r2 < Z.abs b ->
  b*q1+r1 = b*q2+r2 -> q1=q2 /\ r1=r2.
Proof.
intros Hr1 Hr2 H. rewrite <- (Z.abs_sgn b), <- !Z.mul_assoc in H.
destruct (Z.div_mod_unique (Z.abs b) (Z.sgn b * q1) (Z.sgn b * q2) r1 r2); auto.
split; trivial.
apply Z.mul_cancel_l with (Z.sgn b); trivial.
rewrite Z.sgn_null_iff, <- Z.abs_0_iff. destruct Hr1; Z.order.
Qed.

Theorem Zdiv_mod_unique_2 :
 forall b q1 q2 r1 r2:Z,
  Remainder r1 b -> Remainder r2 b ->
  b*q1+r1 = b*q2+r2 -> q1=q2 /\ r1=r2.
Proof Z.div_mod_unique.

Theorem Zdiv_unique_full:
 forall a b q r, Remainder r b ->
   a = b*q + r -> q = a/b.
Proof Z.div_unique.

Theorem Zdiv_unique:
 forall a b q r, 0 <= r < b ->
   a = b*q + r -> q = a/b.
Proof. intros; eapply Zdiv_unique_full; eauto. Qed.

Theorem Zmod_unique_full:
 forall a b q r, Remainder r b ->
  a = b*q + r ->  r = a mod b.
Proof Z.mod_unique.

Theorem Zmod_unique:
 forall a b q r, 0 <= r < b ->
  a = b*q + r -> r = a mod b.
Proof. intros; eapply Zmod_unique_full; eauto. Qed.

(** * Basic values of divisions and modulo. *)

Lemma Zmod_0_l: forall a, 0 mod a = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zmod_0_r: forall a, a mod 0 = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zdiv_0_l: forall a, 0/a = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zdiv_0_r: forall a, a/0 = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Ltac zero_or_not a :=
  destruct (Z.eq_dec a 0);
  [subst; rewrite ?Zmod_0_l, ?Zdiv_0_l, ?Zmod_0_r, ?Zdiv_0_r;
   auto with zarith|].

Lemma Zmod_1_r: forall a, a mod 1 = 0.
Proof. intros. zero_or_not a. apply Z.mod_1_r. Qed.

Lemma Zdiv_1_r: forall a, a/1 = a.
Proof. intros. zero_or_not a. apply Z.div_1_r. Qed.

Hint Resolve Zmod_0_l Zmod_0_r Zdiv_0_l Zdiv_0_r Zdiv_1_r Zmod_1_r
 : zarith.

Lemma Zdiv_1_l: forall a, 1 < a -> 1/a = 0.
Proof Z.div_1_l.

Lemma Zmod_1_l: forall a, 1 < a ->  1 mod a = 1.
Proof Z.mod_1_l.

Lemma Z_div_same_full : forall a:Z, a<>0 -> a/a = 1.
Proof Z.div_same.

Lemma Z_mod_same_full : forall a, a mod a = 0.
Proof. intros. zero_or_not a. apply Z.mod_same; auto. Qed.

Lemma Z_mod_mult : forall a b, (a*b) mod b = 0.
Proof. intros. zero_or_not b. apply Z.mod_mul. auto. Qed.

Lemma Z_div_mult_full : forall a b:Z, b <> 0 -> (a*b)/b = a.
Proof Z.div_mul.

(** * Order results about Z.modulo and Z.div *)

(* Division of positive numbers is positive. *)

Lemma Z_div_pos: forall a b, b > 0 -> 0 <= a -> 0 <= a/b.
Proof. intros. apply Z.div_pos; auto with zarith. Qed.

Lemma Z_div_ge0: forall a b, b > 0 -> a >= 0 -> a/b >=0.
Proof.
  intros; generalize (Z_div_pos a b H); auto with zarith.
Qed.

(** As soon as the divisor is greater or equal than 2,
    the division is strictly decreasing. *)

Lemma Z_div_lt : forall a b:Z, b >= 2 -> a > 0 -> a/b < a.
Proof. intros. apply Z.div_lt; auto with zarith. Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem Zdiv_small: forall a b, 0 <= a < b -> a/b = 0.
Proof Z.div_small.

(** Same situation, in term of modulo: *)

Theorem Zmod_small: forall a n, 0 <= a < n -> a mod n = a.
Proof Z.mod_small.

(** [Z.ge] is compatible with a positive division. *)

Lemma Z_div_ge : forall a b c:Z, c > 0 -> a >= b -> a/c >= b/c.
Proof. intros. apply Z.le_ge. apply Z.div_le_mono; auto with zarith. Qed.

(** Same, with [Z.le]. *)

Lemma Z_div_le : forall a b c:Z, c > 0 -> a <= b -> a/c <= b/c.
Proof. intros. apply Z.div_le_mono; auto with zarith. Qed.

(** With our choice of division, rounding of (a/b) is always done toward bottom: *)

Lemma Z_mult_div_ge : forall a b:Z, b > 0 -> b*(a/b) <= a.
Proof. intros. apply Z.mul_div_le; auto with zarith. Qed.

Lemma Z_mult_div_ge_neg : forall a b:Z, b < 0 -> b*(a/b) >= a.
Proof. intros. apply Z.le_ge. apply Z.mul_div_ge; auto with zarith. Qed.

(** The previous inequalities are exact iff the modulo is zero. *)

Lemma Z_div_exact_full_1 : forall a b:Z, a = b*(a/b) -> a mod b = 0.
Proof. intros a b. zero_or_not b. rewrite Z.div_exact; auto. Qed.

Lemma Z_div_exact_full_2 : forall a b:Z, b <> 0 -> a mod b = 0 -> a = b*(a/b).
Proof. intros; rewrite Z.div_exact; auto. Qed.

(** A modulo cannot grow beyond its starting point. *)

Theorem Zmod_le: forall a b, 0 < b -> 0 <= a -> a mod b <= a.
Proof. intros. apply Z.mod_le; auto. Qed.

(** Some additional inequalities about Z.div. *)

Theorem Zdiv_lt_upper_bound:
  forall a b q, 0 < b -> a < q*b -> a/b < q.
Proof. intros a b q; rewrite Z.mul_comm; apply Z.div_lt_upper_bound. Qed.

Theorem Zdiv_le_upper_bound:
  forall a b q, 0 < b -> a <= q*b -> a/b <= q.
Proof. intros a b q; rewrite Z.mul_comm; apply Z.div_le_upper_bound. Qed.

Theorem Zdiv_le_lower_bound:
  forall a b q, 0 < b -> q*b <= a -> q <= a/b.
Proof. intros a b q; rewrite Z.mul_comm; apply Z.div_le_lower_bound. Qed.

(** A division of respect opposite monotonicity for the divisor *)

Lemma Zdiv_le_compat_l: forall p q r, 0 <= p -> 0 < q < r ->
    p / r <= p / q.
Proof. intros; apply Z.div_le_compat_l; auto with zarith. Qed.

Theorem Zdiv_sgn: forall a b,
  0 <= Z.sgn (a/b) * Z.sgn a * Z.sgn b.
Proof.
  destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith;
  generalize (Z.div_pos (Zpos a) (Zpos b)); unfold Z.div, Z.div_eucl;
  destruct Z.pos_div_eucl as (q,r); destruct r; omega with *.
Qed.

(** * Relations between usual operations and Z.modulo and Z.div *)

Lemma Z_mod_plus_full : forall a b c:Z, (a + b * c) mod c = a mod c.
Proof. intros. zero_or_not c. apply Z.mod_add; auto. Qed.

Lemma Z_div_plus_full : forall a b c:Z, c <> 0 -> (a + b * c) / c = a / c + b.
Proof Z.div_add.

Theorem Z_div_plus_full_l: forall a b c : Z, b <> 0 -> (a * b + c) / b = a + c / b.
Proof Z.div_add_l.

(** [Z.opp] and [Z.div], [Z.modulo].
    Due to the choice of convention for our Euclidean division,
    some of the relations about [Z.opp] and divisions are rather complex. *)

Lemma Zdiv_opp_opp : forall a b:Z, (-a)/(-b) = a/b.
Proof. intros. zero_or_not b. apply Z.div_opp_opp; auto. Qed.

Lemma Zmod_opp_opp : forall a b:Z, (-a) mod (-b) = - (a mod b).
Proof. intros. zero_or_not b. apply Z.mod_opp_opp; auto. Qed.

Lemma Z_mod_zero_opp_full : forall a b:Z, a mod b = 0 -> (-a) mod b = 0.
Proof. intros. zero_or_not b. apply Z.mod_opp_l_z; auto. Qed.

Lemma Z_mod_nz_opp_full : forall a b:Z, a mod b <> 0 ->
 (-a) mod b = b - (a mod b).
Proof. intros. zero_or_not b. apply Z.mod_opp_l_nz; auto. Qed.

Lemma Z_mod_zero_opp_r : forall a b:Z, a mod b = 0 -> a mod (-b) = 0.
Proof. intros. zero_or_not b. apply Z.mod_opp_r_z; auto. Qed.

Lemma Z_mod_nz_opp_r : forall a b:Z, a mod b <> 0 ->
 a mod (-b) = (a mod b) - b.
Proof. intros. zero_or_not b. apply Z.mod_opp_r_nz; auto. Qed.

Lemma Z_div_zero_opp_full : forall a b:Z, a mod b = 0 -> (-a)/b = -(a/b).
Proof. intros. zero_or_not b. apply Z.div_opp_l_z; auto. Qed.

Lemma Z_div_nz_opp_full : forall a b:Z, a mod b <> 0 ->
 (-a)/b = -(a/b)-1.
Proof. intros a b. zero_or_not b. intros; rewrite Z.div_opp_l_nz; auto. Qed.

Lemma Z_div_zero_opp_r : forall a b:Z, a mod b = 0 -> a/(-b) = -(a/b).
Proof. intros. zero_or_not b. apply Z.div_opp_r_z; auto. Qed.

Lemma Z_div_nz_opp_r : forall a b:Z, a mod b <> 0 ->
 a/(-b) = -(a/b)-1.
Proof. intros a b. zero_or_not b. intros; rewrite Z.div_opp_r_nz; auto. Qed.

(** Cancellations. *)

Lemma  Zdiv_mult_cancel_r : forall a b c:Z,
 c <> 0 -> (a*c)/(b*c) = a/b.
Proof. intros. zero_or_not b. apply Z.div_mul_cancel_r; auto. Qed.

Lemma Zdiv_mult_cancel_l : forall a b c:Z,
 c<>0 -> (c*a)/(c*b) = a/b.
Proof.
 intros. rewrite (Z.mul_comm c b); zero_or_not b.
 rewrite (Z.mul_comm b c). apply Z.div_mul_cancel_l; auto.
Qed.

Lemma Zmult_mod_distr_l: forall a b c,
  (c*a) mod (c*b) = c * (a mod b).
Proof.
 intros. zero_or_not c. rewrite (Z.mul_comm c b); zero_or_not b.
 rewrite (Z.mul_comm b c). apply Z.mul_mod_distr_l; auto.
Qed.

Lemma Zmult_mod_distr_r: forall a b c,
  (a*c) mod (b*c) = (a mod b) * c.
Proof.
 intros. zero_or_not b. rewrite (Z.mul_comm b c); zero_or_not c.
 rewrite (Z.mul_comm c b). apply Z.mul_mod_distr_r; auto.
Qed.

(** Operations modulo. *)

Theorem Zmod_mod: forall a n, (a mod n) mod n = a mod n.
Proof. intros. zero_or_not n. apply Z.mod_mod; auto. Qed.

Theorem Zmult_mod: forall a b n,
 (a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof. intros. zero_or_not n. apply Z.mul_mod; auto. Qed.

Theorem Zplus_mod: forall a b n,
 (a + b) mod n = (a mod n + b mod n) mod n.
Proof. intros. zero_or_not n. apply Z.add_mod; auto. Qed.

Theorem Zminus_mod: forall a b n,
 (a - b) mod n = (a mod n - b mod n) mod n.
Proof.
  intros.
  replace (a - b) with (a + (-1) * b); auto with zarith.
  replace (a mod n - b mod n) with (a mod n + (-1) * (b mod n)); auto with zarith.
  rewrite Zplus_mod.
  rewrite Zmult_mod.
  rewrite Zplus_mod with (b:=(-1) * (b mod n)).
  rewrite Zmult_mod.
  rewrite Zmult_mod with (b:= b mod n).
  repeat rewrite Zmod_mod; auto.
Qed.

Lemma Zplus_mod_idemp_l: forall a b n, (a mod n + b) mod n = (a + b) mod n.
Proof.
  intros; rewrite Zplus_mod, Zmod_mod, <- Zplus_mod; auto.
Qed.

Lemma Zplus_mod_idemp_r: forall a b n, (b + a mod n) mod n = (b + a) mod n.
Proof.
  intros; rewrite Zplus_mod, Zmod_mod, <- Zplus_mod; auto.
Qed.

Lemma Zminus_mod_idemp_l: forall a b n, (a mod n - b) mod n = (a - b) mod n.
Proof.
  intros; rewrite Zminus_mod, Zmod_mod, <- Zminus_mod; auto.
Qed.

Lemma Zminus_mod_idemp_r: forall a b n, (a - b mod n) mod n = (a - b) mod n.
Proof.
  intros; rewrite Zminus_mod, Zmod_mod, <- Zminus_mod; auto.
Qed.

Lemma Zmult_mod_idemp_l: forall a b n, (a mod n * b) mod n = (a * b) mod n.
Proof.
  intros; rewrite Zmult_mod, Zmod_mod, <- Zmult_mod; auto.
Qed.

Lemma Zmult_mod_idemp_r: forall a b n, (b * (a mod n)) mod n = (b * a) mod n.
Proof.
  intros; rewrite Zmult_mod, Zmod_mod, <- Zmult_mod; auto.
Qed.

(** For a specific number N, equality modulo N is hence a nice setoid
   equivalence, compatible with [+], [-] and [*]. *)

Section EqualityModulo.
Variable N:Z.

Definition eqm a b := (a mod N = b mod N).
Infix "==" := eqm (at level 70).

Lemma eqm_refl : forall a, a == a.
Proof. unfold eqm; auto. Qed.

Lemma eqm_sym : forall a b, a == b -> b == a.
Proof. unfold eqm; auto. Qed.

Lemma eqm_trans : forall a b c,
  a == b -> b == c -> a == c.
Proof. unfold eqm; eauto with *. Qed.

Instance eqm_setoid : Equivalence eqm.
Proof.
 constructor; [exact eqm_refl | exact eqm_sym | exact eqm_trans].
Qed.

Instance Zplus_eqm : Proper (eqm ==> eqm ==> eqm) Z.add.
Proof.
  unfold eqm; repeat red; intros. rewrite Zplus_mod, H, H0, <- Zplus_mod; auto.
Qed.

Instance Zminus_eqm : Proper (eqm ==> eqm ==> eqm) Z.sub.
Proof.
  unfold eqm; repeat red; intros. rewrite Zminus_mod, H, H0, <- Zminus_mod; auto.
Qed.

Instance Zmult_eqm : Proper (eqm ==> eqm ==> eqm) Z.mul.
Proof.
  unfold eqm; repeat red; intros. rewrite Zmult_mod, H, H0, <- Zmult_mod; auto.
Qed.

Instance Zopp_eqm : Proper (eqm ==> eqm) Z.opp.
Proof.
  intros x y H. change ((-x)==(-y)) with ((0-x)==(0-y)). now rewrite H.
Qed.

Lemma Zmod_eqm : forall a, (a mod N) == a.
Proof.
  intros; exact (Zmod_mod a N).
Qed.

(* NB: Z.modulo and Z.div are not morphisms with respect to eqm.
    For instance, let (==) be (eqm 2). Then we have (3 == 1) but:
    ~ (3 mod 3 == 1 mod 3)
    ~ (1 mod 3 == 1 mod 1)
    ~ (3/3 == 1/3)
    ~ (1/3 == 1/1)
*)

End EqualityModulo.

Lemma Zdiv_Zdiv : forall a b c, 0<=b -> 0<=c -> (a/b)/c = a/(b*c).
Proof.
 intros. zero_or_not b. rewrite Z.mul_comm. zero_or_not c.
 rewrite Z.mul_comm. apply Z.div_div; auto with zarith.
Qed.

(** Unfortunately, the previous result isn't always true on negative numbers.
    For instance: 3/(-2)/(-2) = 1 <> 0 = 3 / (-2*-2) *)

Lemma Zmod_div : forall a b, a mod b / b = 0.
Proof.
 intros a b.
 zero_or_not b.
 auto using Z.mod_div.
Qed.

(** A last inequality: *)

Theorem Zdiv_mult_le:
 forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof.
 intros. zero_or_not b. apply Z.div_mul_le; auto with zarith. Qed.

(** Z.modulo is related to divisibility (see more in Znumtheory) *)

Lemma Zmod_divides : forall a b, b<>0 ->
 (a mod b = 0 <-> exists c, a = b*c).
Proof.
 intros. rewrite Z.mod_divide; trivial.
 split; intros (c,Hc); exists c; subst; auto with zarith.
Qed.

(** Particular case : dividing by 2 is related with parity *)

Lemma Zdiv2_div : forall a, Z.div2 a = a/2.
Proof Z.div2_div.

Lemma Zmod_odd : forall a, a mod 2 = if Z.odd a then 1 else 0.
Proof.
 intros a. now rewrite <- Z.bit0_odd, <- Z.bit0_mod.
Qed.

Lemma Zmod_even : forall a, a mod 2 = if Z.even a then 0 else 1.
Proof.
 intros a. rewrite Zmod_odd, Zodd_even_bool. now destruct Z.even.
Qed.

Lemma Zodd_mod : forall a, Z.odd a = Zeq_bool (a mod 2) 1.
Proof.
 intros a. rewrite Zmod_odd. now destruct Z.odd.
Qed.

Lemma Zeven_mod : forall a, Z.even a = Zeq_bool (a mod 2) 0.
Proof.
 intros a. rewrite Zmod_even. now destruct Z.even.
Qed.

(** * Compatibility *)

(** Weaker results kept only for compatibility *)

Lemma Z_mod_same : forall a, a > 0 -> a mod a = 0.
Proof.
  intros; apply Z_mod_same_full.
Qed.

Lemma Z_div_same : forall a, a > 0 -> a/a = 1.
Proof.
  intros; apply Z_div_same_full; auto with zarith.
Qed.

Lemma Z_div_plus : forall a b c:Z, c > 0 -> (a + b * c) / c = a / c + b.
Proof.
  intros; apply Z_div_plus_full; auto with zarith.
Qed.

Lemma Z_div_mult : forall a b:Z, b > 0 -> (a*b)/b = a.
Proof.
  intros; apply Z_div_mult_full; auto with zarith.
Qed.

Lemma Z_mod_plus : forall a b c:Z, c > 0 -> (a + b * c) mod c = a mod c.
Proof.
  intros; apply Z_mod_plus_full; auto with zarith.
Qed.

Lemma Z_div_exact_1 : forall a b:Z, b > 0 -> a = b*(a/b) -> a mod b = 0.
Proof.
  intros; apply Z_div_exact_full_1; auto with zarith.
Qed.

Lemma Z_div_exact_2 : forall a b:Z, b > 0 -> a mod b = 0 -> a = b*(a/b).
Proof.
  intros; apply Z_div_exact_full_2; auto with zarith.
Qed.

Lemma Z_mod_zero_opp : forall a b:Z, b > 0 -> a mod b = 0 -> (-a) mod b = 0.
Proof.
  intros; apply Z_mod_zero_opp_full; auto with zarith.
Qed.

(** * A direct way to compute Z.modulo *)

Fixpoint Zmod_POS (a : positive) (b : Z) : Z  :=
  match a with
   | xI a' =>
      let r := Zmod_POS a' b in
      let r' := (2 * r + 1) in
      if r' <? b then r' else (r' - b)
   | xO a' =>
      let r := Zmod_POS a' b in
      let r' := (2 * r) in
      if r' <? b then r' else (r' - b)
   | xH => if 2 <=? b then 1 else 0
  end.

Definition Zmod' a b :=
  match a with
   | Z0 => 0
   | Zpos a' =>
      match b with
       | Z0 => 0
       | Zpos _ => Zmod_POS a' b
       | Zneg b' =>
          let r := Zmod_POS a' (Zpos b') in
          match r  with Z0 =>  0 |  _  =>   b + r end
      end
   | Zneg a' =>
      match b with
       | Z0 => 0
       | Zpos _ =>
          let r := Zmod_POS a' b in
          match r with Z0 =>  0 | _  =>  b - r end
       | Zneg b' => - (Zmod_POS a' (Zpos b'))
      end
  end.


Theorem Zmod_POS_correct a b : Zmod_POS a b = snd (Z.pos_div_eucl a b).
Proof.
  induction a as [a IH|a IH| ]; simpl; rewrite ?IH.
  destruct (Z.pos_div_eucl a b) as (p,q); simpl;
   case Z.ltb_spec; reflexivity.
  destruct (Z.pos_div_eucl a b) as (p,q); simpl;
   case Z.ltb_spec; reflexivity.
  case Z.leb_spec; trivial.
Qed.

Theorem Zmod'_correct: forall a b, Zmod' a b = a mod b.
Proof.
  intros a b; unfold Z.modulo; case a; simpl; auto.
  intros p; case b; simpl; auto.
  intros p1; refine (Zmod_POS_correct _ _); auto.
  intros p1; rewrite Zmod_POS_correct; auto.
  case (Z.pos_div_eucl p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
  intros p; case b; simpl; auto.
  intros p1; rewrite Zmod_POS_correct; auto.
  case (Z.pos_div_eucl p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
  intros p1; rewrite Zmod_POS_correct; simpl; auto.
  case (Z.pos_div_eucl p (Zpos p1)); auto.
Qed.


(** Another convention is possible for division by negative numbers:
    * quotient is always the biggest integer smaller than or equal to a/b
    * remainder is hence always positive or null. *)

Theorem Zdiv_eucl_extended :
  forall b:Z,
    b <> 0 ->
    forall a:Z,
      {qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < Z.abs b}.
Proof.
  intros b Hb a.
  destruct (Z_le_gt_dec 0 b) as [Hb'|Hb'].
  - assert (Hb'' : b > 0) by omega.
    rewrite Z.abs_eq; [ apply Zdiv_eucl_exist; assumption | assumption ].
  - assert (Hb'' : - b > 0) by omega.
    destruct (Zdiv_eucl_exist Hb'' a) as ((q,r),[]).
    exists (- q, r).
    split.
    + rewrite <- Z.mul_opp_comm; assumption.
    + rewrite Z.abs_neq; [ assumption | omega ].
Qed.

Arguments Zdiv_eucl_extended : default implicits.

(** * Division and modulo in Z agree with same in nat: *)

Require Import PeanoNat.

Lemma div_Zdiv (n m: nat): m <> O ->
  Z.of_nat (n / m) = Z.of_nat n / Z.of_nat m.
Proof.
 intros.
 apply (Zdiv_unique _ _ _ (Z.of_nat (n mod m))).
  split. auto with zarith.
  now apply inj_lt, Nat.mod_upper_bound.
 rewrite <- Nat2Z.inj_mul, <- Nat2Z.inj_add.
 now apply inj_eq, Nat.div_mod.
Qed.

Lemma mod_Zmod (n m: nat): m <> O ->
  Z.of_nat (n mod m) = (Z.of_nat n) mod (Z.of_nat m).
Proof.
 intros.
 apply (Zmod_unique _ _ (Z.of_nat n / Z.of_nat m)).
  split. auto with zarith.
  now apply inj_lt, Nat.mod_upper_bound.
 rewrite <- div_Zdiv, <- Nat2Z.inj_mul, <- Nat2Z.inj_add by trivial.
 now apply inj_eq, Nat.div_mod.
Qed.
