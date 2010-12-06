(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Euclidean Division *)

(** Initial Contribution by Claude Marché and Xavier Urbain *)

Require Export ZArith_base Zdiv_def.
Require Import Zbool Omega ZArithRing Zcomplements Setoid Morphisms.
Require ZDivFloor.
Local Open Scope Z_scope.

(** The definition and initial properties are now in file [Zdiv_def] *)

(** * Main division theorems *)

(** NB: many things are stated twice for compatibility reasons *)

Lemma Z_div_mod_POS :
  forall b:Z,
    b > 0 ->
    forall a:positive,
      let (q, r) := Zdiv_eucl_POS a b in Zpos a = b * q + r /\ 0 <= r < b.
Proof.
 intros b Hb a. apply Zgt_lt in Hb.
 generalize (Zdiv_eucl_POS_eq a b Hb) (Zmod_POS_bound a b Hb).
 destruct Zdiv_eucl_POS. auto.
Qed.

Theorem Z_div_mod :
  forall a b:Z,
    b > 0 -> let (q, r) := Zdiv_eucl a b in a = b * q + r /\ 0 <= r < b.
Proof.
 intros a b Hb. apply Zgt_lt in Hb.
 assert (Hb' : b<>0) by (now destruct b).
 generalize (Zdiv_eucl_eq a b Hb') (Zmod_pos_bound a b Hb).
 unfold Zmod. destruct Zdiv_eucl. auto.
Qed.

(** For stating the fully general result, let's give a short name
    to the condition on the remainder. *)

Definition Remainder r b :=  0 <= r < b \/ b < r <= 0.

(** Another equivalent formulation: *)

Definition Remainder_alt r b :=  Zabs r < Zabs b /\ Zsgn r <> - Zsgn b.

(* In the last formulation, [ Zsgn r <> - Zsgn b ] is less nice than saying
    [ Zsgn r = Zsgn b ], but at least it works even when [r] is null. *)

Lemma Remainder_equiv : forall r b, Remainder r b <-> Remainder_alt r b.
Proof.
 intros; unfold Remainder, Remainder_alt; omega with *.
Qed.

Hint Unfold Remainder.

(** Now comes the fully general result about Euclidean division. *)

Theorem Z_div_mod_full :
  forall a b:Z,
    b <> 0 -> let (q, r) := Zdiv_eucl a b in a = b * q + r /\ Remainder r b.
Proof.
 intros a b Hb.
 generalize (Zdiv_eucl_eq a b Hb)
  (Zmod_pos_bound a b) (Zmod_neg_bound a b).
 unfold Zmod. destruct Zdiv_eucl as (q,r).
 intros EQ POS NEG.
 split; auto.
 red; destruct b.
  now destruct Hb. left; now apply POS. right; now apply NEG.
Qed.

(** The same results as before, stated separately in terms of Zdiv and Zmod *)

Lemma Z_mod_remainder : forall a b:Z, b<>0 -> Remainder (a mod b) b.
Proof.
  unfold Zmod; intros a b Hb; generalize (Z_div_mod_full a b Hb); auto.
  destruct Zdiv_eucl; tauto.
Qed.

Definition Z_mod_lt : forall a b:Z, b > 0 -> 0 <= a mod b < b
 := fun a b Hb => Zmod_pos_bound a b (Zgt_lt _ _ Hb).

Definition Z_mod_neg : forall a b:Z, b < 0 -> b < a mod b <= 0
 := Zmod_neg_bound.

Notation Z_div_mod_eq_full := Z_div_mod_eq_full (only parsing).

Lemma Z_div_mod_eq : forall a b:Z, b > 0 -> a = b*(a/b) + (a mod b).
Proof.
  intros; apply Z_div_mod_eq_full; auto with zarith.
Qed.

Lemma Zmod_eq_full : forall a b:Z, b<>0 -> a mod b = a - (a/b)*b.
Proof. intros. rewrite Zmult_comm. now apply Z.mod_eq. Qed.

Lemma Zmod_eq : forall a b:Z, b>0 -> a mod b = a - (a/b)*b.
Proof. intros. apply Zmod_eq_full. now destruct b. Qed.

(** Existence theorem *)

Theorem Zdiv_eucl_exist : forall (b:Z)(Hb:b>0)(a:Z),
 {qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < b}.
Proof.
  intros b Hb a.
  exists (Zdiv_eucl a b).
  exact (Z_div_mod a b Hb).
Qed.

Implicit Arguments Zdiv_eucl_exist.


(** Uniqueness theorems *)

Theorem Zdiv_mod_unique :
 forall b q1 q2 r1 r2:Z,
  0 <= r1 < Zabs b -> 0 <= r2 < Zabs b ->
  b*q1+r1 = b*q2+r2 -> q1=q2 /\ r1=r2.
Proof.
intros b q1 q2 r1 r2 Hr1 Hr2 H.
destruct (Z_eq_dec q1 q2) as [Hq|Hq].
split; trivial.
rewrite Hq in H; omega.
elim (Zlt_not_le (Zabs (r2 - r1)) (Zabs b)).
omega with *.
replace (r2-r1) with (b*(q1-q2)) by (rewrite Zmult_minus_distr_l; omega).
replace (Zabs b) with ((Zabs b)*1) by ring.
rewrite Zabs_Zmult.
apply Zmult_le_compat_l; auto with *.
omega with *.
Qed.

Theorem Zdiv_mod_unique_2 :
 forall b q1 q2 r1 r2:Z,
  Remainder r1 b -> Remainder r2 b ->
  b*q1+r1 = b*q2+r2 -> q1=q2 /\ r1=r2.
Proof. exact Z.div_mod_unique. Qed.

Theorem Zdiv_unique_full:
 forall a b q r, Remainder r b ->
   a = b*q + r -> q = a/b.
Proof. exact Z.div_unique. Qed.

Theorem Zdiv_unique:
 forall a b q r, 0 <= r < b ->
   a = b*q + r -> q = a/b.
Proof. intros; eapply Zdiv_unique_full; eauto. Qed.

Theorem Zmod_unique_full:
 forall a b q r, Remainder r b ->
  a = b*q + r ->  r = a mod b.
Proof. exact Z.mod_unique. Qed.

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
  destruct (Z_eq_dec a 0);
  [subst; rewrite ?Zmod_0_l, ?Zdiv_0_l, ?Zmod_0_r, ?Zdiv_0_r;
   auto with zarith|].

Lemma Zmod_1_r: forall a, a mod 1 = 0.
Proof. intros. zero_or_not a. apply Z.mod_1_r. Qed.

Lemma Zdiv_1_r: forall a, a/1 = a.
Proof. intros. zero_or_not a. apply Z.div_1_r. Qed.

Hint Resolve Zmod_0_l Zmod_0_r Zdiv_0_l Zdiv_0_r Zdiv_1_r Zmod_1_r
 : zarith.

Lemma Zdiv_1_l: forall a, 1 < a -> 1/a = 0.
Proof. exact Z.div_1_l. Qed.

Lemma Zmod_1_l: forall a, 1 < a ->  1 mod a = 1.
Proof. exact Z.mod_1_l. Qed.

Lemma Z_div_same_full : forall a:Z, a<>0 -> a/a = 1.
Proof. exact Z.div_same. Qed.

Lemma Z_mod_same_full : forall a, a mod a = 0.
Proof. intros. zero_or_not a. apply Z.mod_same; auto. Qed.

Lemma Z_mod_mult : forall a b, (a*b) mod b = 0.
Proof. intros. zero_or_not b. apply Z.mod_mul. auto. Qed.

Lemma Z_div_mult_full : forall a b:Z, b <> 0 -> (a*b)/b = a.
Proof. exact Z.div_mul. Qed.

(** * Order results about Zmod and Zdiv *)

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
Proof. exact Z.div_small. Qed.

(** Same situation, in term of modulo: *)

Theorem Zmod_small: forall a n, 0 <= a < n -> a mod n = a.
Proof. exact Z.mod_small. Qed.

(** [Zge] is compatible with a positive division. *)

Lemma Z_div_ge : forall a b c:Z, c > 0 -> a >= b -> a/c >= b/c.
Proof. intros. apply Zle_ge. apply Z.div_le_mono; auto with zarith. Qed.

(** Same, with [Zle]. *)

Lemma Z_div_le : forall a b c:Z, c > 0 -> a <= b -> a/c <= b/c.
Proof. intros. apply Z.div_le_mono; auto with zarith. Qed.

(** With our choice of division, rounding of (a/b) is always done toward bottom: *)

Lemma Z_mult_div_ge : forall a b:Z, b > 0 -> b*(a/b) <= a.
Proof. intros. apply Z.mul_div_le; auto with zarith. Qed.

Lemma Z_mult_div_ge_neg : forall a b:Z, b < 0 -> b*(a/b) >= a.
Proof. intros. apply Zle_ge. apply Z.mul_div_ge; auto with zarith. Qed.

(** The previous inequalities are exact iff the modulo is zero. *)

Lemma Z_div_exact_full_1 : forall a b:Z, a = b*(a/b) -> a mod b = 0.
Proof. intros a b. zero_or_not b. rewrite Z.div_exact; auto. Qed.

Lemma Z_div_exact_full_2 : forall a b:Z, b <> 0 -> a mod b = 0 -> a = b*(a/b).
Proof. intros; rewrite Z.div_exact; auto. Qed.

(** A modulo cannot grow beyond its starting point. *)

Theorem Zmod_le: forall a b, 0 < b -> 0 <= a -> a mod b <= a.
Proof. intros. apply Z.mod_le; auto. Qed.

(** Some additionnal inequalities about Zdiv. *)

Theorem Zdiv_lt_upper_bound:
  forall a b q, 0 < b -> a < q*b -> a/b < q.
Proof. intros a b q; rewrite Zmult_comm; apply Z.div_lt_upper_bound. Qed.

Theorem Zdiv_le_upper_bound:
  forall a b q, 0 < b -> a <= q*b -> a/b <= q.
Proof. intros a b q; rewrite Zmult_comm; apply Z.div_le_upper_bound. Qed.

Theorem Zdiv_le_lower_bound:
  forall a b q, 0 < b -> q*b <= a -> q <= a/b.
Proof. intros a b q; rewrite Zmult_comm; apply Z.div_le_lower_bound. Qed.

(** A division of respect opposite monotonicity for the divisor *)

Lemma Zdiv_le_compat_l: forall p q r, 0 <= p -> 0 < q < r ->
    p / r <= p / q.
Proof. intros; apply Z.div_le_compat_l; auto with zarith. Qed.

Theorem Zdiv_sgn: forall a b,
  0 <= Zsgn (a/b) * Zsgn a * Zsgn b.
Proof.
  destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith;
  generalize (Z_div_pos (Zpos a) (Zpos b)); unfold Zdiv, Zdiv_eucl;
  destruct Zdiv_eucl_POS as (q,r); destruct r; omega with *.
Qed.

(** * Relations between usual operations and Zmod and Zdiv *)

Lemma Z_mod_plus_full : forall a b c:Z, (a + b * c) mod c = a mod c.
Proof. intros. zero_or_not c. apply Z.mod_add; auto. Qed.

Lemma Z_div_plus_full : forall a b c:Z, c <> 0 -> (a + b * c) / c = a / c + b.
Proof. exact Z.div_add. Qed.

Theorem Z_div_plus_full_l: forall a b c : Z, b <> 0 -> (a * b + c) / b = a + c / b.
Proof. exact Z.div_add_l. Qed.

(** [Zopp] and [Zdiv], [Zmod].
    Due to the choice of convention for our Euclidean division,
    some of the relations about [Zopp] and divisions are rather complex. *)

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
 intros. rewrite (Zmult_comm c b); zero_or_not b.
 rewrite (Zmult_comm b c). apply Z.div_mul_cancel_l; auto.
Qed.

Lemma Zmult_mod_distr_l: forall a b c,
  (c*a) mod (c*b) = c * (a mod b).
Proof.
 intros. zero_or_not c. rewrite (Zmult_comm c b); zero_or_not b.
 rewrite (Zmult_comm b c). apply Z.mul_mod_distr_l; auto.
Qed.

Lemma Zmult_mod_distr_r: forall a b c,
  (a*c) mod (b*c) = (a mod b) * c.
Proof.
 intros. zero_or_not b. rewrite (Zmult_comm b c); zero_or_not c.
 rewrite (Zmult_comm c b). apply Z.mul_mod_distr_r; auto.
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

Definition eqm N a b := (a mod N = b mod N).

Lemma eqm_refl N : forall a, (eqm N) a a.
Proof. unfold eqm; auto. Qed.

Lemma eqm_sym N : forall a b, (eqm N) a b -> (eqm N) b a.
Proof. unfold eqm; auto. Qed.

Lemma eqm_trans N : forall a b c,
  (eqm N) a b -> (eqm N) b c -> (eqm N) a c.
Proof. unfold eqm; eauto with *. Qed.

Add Parametric Relation N : Z (eqm N)
  reflexivity proved by (eqm_refl N)
  symmetry proved by (eqm_sym N)
  transitivity proved by (eqm_trans N) as eqm_setoid.

Add Parametric Morphism N : Zplus
  with signature (eqm N) ==> (eqm N) ==> (eqm N) as Zplus_eqm.
Proof.
  unfold eqm; intros; rewrite Zplus_mod, H, H0, <- Zplus_mod; auto.
Qed.

Add Parametric Morphism N : Zminus
  with signature (eqm N) ==> (eqm N) ==> (eqm N) as Zminus_eqm.
Proof.
  unfold eqm; intros; rewrite Zminus_mod, H, H0, <- Zminus_mod; auto.
Qed.

Add Parametric Morphism N : Zmult
  with signature (eqm N) ==> (eqm N) ==> (eqm N) as Zmult_eqm.
Proof.
  unfold eqm; intros; rewrite Zmult_mod, H, H0, <- Zmult_mod; auto.
Qed.

Add Parametric Morphism N : Zopp
  with signature (eqm N) ==> (eqm N) as Zopp_eqm.
Proof.
  intros; change ((eqm N) (-x) (-y)) with ((eqm N) (0-x) (0-y)).
  rewrite H; red; auto.
Qed.

Lemma Zmod_eqm N : forall a, (eqm N) (a mod N) a.
Proof.
  intros; exact (Zmod_mod a N).
Qed.

(* NB: Zmod and Zdiv are not morphisms with respect to eqm.
    For instance, let (==) be (eqm 2). Then we have (3 == 1) but:
    ~ (3 mod 3 == 1 mod 3)
    ~ (1 mod 3 == 1 mod 1)
    ~ (3/3 == 1/3)
    ~ (1/3 == 1/1)
*)

Lemma Zdiv_Zdiv : forall a b c, 0<=b -> 0<=c -> (a/b)/c = a/(b*c).
Proof.
 intros. zero_or_not b. rewrite Zmult_comm. zero_or_not c.
 rewrite Zmult_comm. apply Z.div_div; auto with zarith.
Qed.

(** Unfortunately, the previous result isn't always true on negative numbers.
    For instance: 3/(-2)/(-2) = 1 <> 0 = 3 / (-2*-2) *)

(** A last inequality: *)

Theorem Zdiv_mult_le:
 forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof.
 intros. zero_or_not b. apply Z.div_mul_le; auto with zarith. Qed.

(** Zmod is related to divisibility (see more in Znumtheory) *)

Lemma Zmod_divides : forall a b, b<>0 ->
 (a mod b = 0 <-> exists c, a = b*c).
Proof.
 intros. rewrite Z.mod_divide; trivial.
 split; intros (c,Hc); exists c; auto.
Qed.

(** Particular case : dividing by 2 is related with parity *)

Lemma Zdiv2'_div : forall a, Zdiv2' a = a/2.
Proof.
 apply Z.div2_div.
Qed.

Lemma Zmod_odd : forall a, a mod 2 = if Zodd_bool a then 1 else 0.
Proof.
 intros a. now rewrite <- Z.bit0_odd, <- Z.bit0_mod.
Qed.

Lemma Zmod_even : forall a, a mod 2 = if Zeven_bool a then 0 else 1.
Proof.
 intros a. rewrite Zmod_odd, Zodd_even_bool. now destruct Zeven_bool.
Qed.

Lemma Zodd_mod : forall a, Zodd_bool a = Zeq_bool (a mod 2) 1.
Proof.
 intros a. rewrite Zmod_odd. now destruct Zodd_bool.
Qed.

Lemma Zeven_mod : forall a, Zeven_bool a = Zeq_bool (a mod 2) 0.
Proof.
 intros a. rewrite Zmod_even. now destruct Zeven_bool.
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

(** * A direct way to compute Zmod *)

Fixpoint Zmod_POS (a : positive) (b : Z) : Z  :=
  match a with
   | xI a' =>
      let r := Zmod_POS a' b in
      let r' := (2 * r + 1) in
      if Zgt_bool b r' then r' else (r' - b)
   | xO a' =>
      let r := Zmod_POS a' b in
      let r' := (2 * r) in
      if Zgt_bool b r' then r' else (r' - b)
   | xH => if Zge_bool b 2 then 1 else 0
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


Theorem Zmod_POS_correct: forall a b, Zmod_POS a b = (snd (Zdiv_eucl_POS a b)).
Proof.
  intros a b; elim a; simpl; auto.
  intros p Rec; rewrite  Rec.
  case (Zdiv_eucl_POS p b); intros z1 z2; simpl; auto.
  match goal with |- context [Zgt_bool _ ?X] => case (Zgt_bool b X) end; auto.
  intros p Rec; rewrite  Rec.
  case (Zdiv_eucl_POS p b); intros z1 z2; simpl; auto.
  match goal with |- context [Zgt_bool _ ?X] => case (Zgt_bool b X) end; auto.
  case (Zge_bool b 2); auto.
Qed.

Theorem Zmod'_correct: forall a b, Zmod' a b = Zmod a b.
Proof.
  intros a b; unfold Zmod; case a; simpl; auto.
  intros p; case b; simpl; auto.
  intros p1; refine (Zmod_POS_correct _ _); auto.
  intros p1; rewrite Zmod_POS_correct; auto.
  case (Zdiv_eucl_POS p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
  intros p; case b; simpl; auto.
  intros p1; rewrite Zmod_POS_correct; auto.
  case (Zdiv_eucl_POS p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
  intros p1; rewrite Zmod_POS_correct; simpl; auto.
  case (Zdiv_eucl_POS p (Zpos p1)); auto.
Qed.


(** Another convention is possible for division by negative numbers:
    * quotient is always the biggest integer smaller than or equal to a/b
    * remainder is hence always positive or null. *)

Theorem Zdiv_eucl_extended :
  forall b:Z,
    b <> 0 ->
    forall a:Z,
      {qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < Zabs b}.
Proof.
  intros b Hb a.
  elim (Z_le_gt_dec 0 b); intro Hb'.
  cut (b > 0); [ intro Hb'' | omega ].
  rewrite Zabs_eq; [ apply Zdiv_eucl_exist; assumption | assumption ].
  cut (- b > 0); [ intro Hb'' | omega ].
  elim (Zdiv_eucl_exist Hb'' a); intros qr.
  elim qr; intros q r Hqr.
  exists (- q, r).
  elim Hqr; intros.
  split.
  rewrite <- Zmult_opp_comm; assumption.
  rewrite Zabs_non_eq; [ assumption | omega ].
Qed.

Implicit Arguments Zdiv_eucl_extended.

(** * Division and modulo in Z agree with same in nat: *)

Require Import NPeano.

Lemma div_Zdiv (n m: nat): m <> O ->
  Z_of_nat (n / m) = Z_of_nat n / Z_of_nat m.
Proof.
 intros.
 apply (Zdiv_unique _ _ _ (Z_of_nat (n mod m)%nat)).
  split. auto with zarith.
  now apply inj_lt, Nat.mod_upper_bound.
 rewrite <- inj_mult, <- inj_plus.
 now apply inj_eq, Nat.div_mod.
Qed.

Lemma mod_Zmod (n m: nat): m <> O ->
  Z_of_nat (n mod m)%nat = (Z_of_nat n mod Z_of_nat m).
Proof.
 intros.
 apply (Zmod_unique _ _ (Z_of_nat n / Z_of_nat m)).
  split. auto with zarith.
  now apply inj_lt, Nat.mod_upper_bound.
 rewrite <- div_Zdiv, <- inj_mult, <- inj_plus by trivial.
 now apply inj_eq, Nat.div_mod.
Qed.


(** For compatibility *)

Notation Zdiv_eucl := Zdiv_eucl (only parsing).
Notation Zdiv := Zdiv (only parsing).
Notation Zmod := Zmod (only parsing).
