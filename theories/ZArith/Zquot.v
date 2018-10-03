(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Nnat ZArith_base Lia ZArithRing Zdiv Morphisms.

Local Open Scope Z_scope.

(** This file provides results about the Round-Toward-Zero Euclidean
  division [Z.quotrem], whose projections are [Z.quot] (noted ÷)
  and [Z.rem].

  This division and [Z.div] agree only on positive numbers.
  Otherwise, [Z.div] performs Round-Toward-Bottom (a.k.a Floor).

  This [Z.quot] is compatible with the division of usual
  programming languages such as Ocaml. In addition, it has nicer
  properties with respect to opposite and other usual operations.

  The definition of this division is now in file [BinIntDef],
  while most of the results about here are now in the main module
  [BinInt.Z], thanks to the generic "Numbers" layer. Remain here:

  - some compatibility notation for old names.

  - some extra results with less preconditions (in particular
      exploiting the arbitrary value of division by 0).
*)

Notation Ndiv_Zquot := N2Z.inj_quot (only parsing).
Notation Nmod_Zrem := N2Z.inj_rem (only parsing).
Notation Z_quot_rem_eq := Z.quot_rem' (only parsing).
Notation Zrem_lt := Z.rem_bound_abs (only parsing).
Notation Zquot_unique := Z.quot_unique (compat "8.7").
Notation Zrem_unique := Z.rem_unique (compat "8.7").
Notation Zrem_1_r := Z.rem_1_r (compat "8.7").
Notation Zquot_1_r := Z.quot_1_r (compat "8.7").
Notation Zrem_1_l := Z.rem_1_l (compat "8.7").
Notation Zquot_1_l := Z.quot_1_l (compat "8.7").
Notation Z_quot_same := Z.quot_same (compat "8.7").
Notation Z_quot_mult := Z.quot_mul (only parsing).
Notation Zquot_small := Z.quot_small (compat "8.7").
Notation Zrem_small := Z.rem_small (compat "8.7").
Notation Zquot2_quot := Zquot2_quot (compat "8.7").

(** Particular values taken for [a÷0] and [(Z.rem a 0)].
    We avise to not rely on these arbitrary values. *)

Lemma Zquot_0_r a : a ÷ 0 = 0.
Proof. now destruct a. Qed.

Lemma Zrem_0_r a : Z.rem a 0 = a.
Proof. now destruct a. Qed.

(** The following results are expressed without the [b<>0] condition
    whenever possible. *)

Lemma Zrem_0_l a : Z.rem 0 a = 0.
Proof. now destruct a. Qed.

Lemma Zquot_0_l a : 0÷a = 0.
Proof. now destruct a. Qed.

Hint Resolve Zrem_0_l Zrem_0_r Zquot_0_l Zquot_0_r Z.quot_1_r Z.rem_1_r
 : zarith.

Ltac zero_or_not a :=
  destruct (Z.eq_decidable a 0) as [->|?];
  [rewrite ?Zquot_0_l, ?Zrem_0_l, ?Zquot_0_r, ?Zrem_0_r;
   auto with zarith|].

Lemma Z_rem_same a : Z.rem a a = 0.
Proof. zero_or_not a. now apply Z.rem_same. Qed.

Lemma Z_rem_mult a b : Z.rem (a*b) b = 0.
Proof. zero_or_not b. now apply Z.rem_mul. Qed.

(** * Division and Opposite *)

(* The precise equalities that are invalid with "historic" Zdiv. *)

Theorem Zquot_opp_l a b : (-a)÷b = -(a÷b).
Proof. zero_or_not b. now apply Z.quot_opp_l. Qed.

Theorem Zquot_opp_r a b : a÷(-b) = -(a÷b).
Proof. zero_or_not b. now apply Z.quot_opp_r. Qed.

Theorem Zrem_opp_l a b : Z.rem (-a) b = -(Z.rem a b).
Proof. zero_or_not b. now apply Z.rem_opp_l. Qed.

Theorem Zrem_opp_r a b : Z.rem a (-b) = Z.rem a b.
Proof. zero_or_not b. now apply Z.rem_opp_r. Qed.

Theorem Zquot_opp_opp a b : (-a)÷(-b) = a÷b.
Proof. zero_or_not b. now apply Z.quot_opp_opp. Qed.

Theorem Zrem_opp_opp a b : Z.rem (-a) (-b) = -(Z.rem a b).
Proof. zero_or_not b. now apply Z.rem_opp_opp. Qed.

(** The sign of the remainder is the one of [a]. Due to the possible
   nullity of [a], a general result is to be stated in the following form:
*)

Theorem Zrem_sgn a b : 0 <= Z.sgn (Z.rem a b) * Z.sgn a.
Proof.
  zero_or_not b.
  - apply Z.square_nonneg.
  - zero_or_not (Z.rem a b).
    rewrite Z.rem_sign_nz; trivial. apply Z.square_nonneg.
Qed.

(** This can also be said in a simplier way: *)

Theorem Zrem_sgn2 a b : 0 <= (Z.rem a b) * a.
Proof.
  zero_or_not b.
  - apply Z.square_nonneg.
  - now apply Z.rem_sign_mul.
Qed.

(** Reformulation of [Z.rem_bound_abs] in 2 then 4 particular cases. *)

Theorem Zrem_lt_pos a b : 0<=a -> b<>0 -> 0 <= Z.rem a b < Z.abs b.
Proof.
  intros; generalize (Z.rem_nonneg a b) (Z.rem_bound_abs a b);
    lia.
Qed.

Theorem Zrem_lt_neg a b : a<=0 -> b<>0 -> -Z.abs b < Z.rem a b <= 0.
Proof.
  intros; generalize (Z.rem_nonpos a b) (Z.rem_bound_abs a b);
   lia.
Qed.

Theorem Zrem_lt_pos_pos a b : 0<=a -> 0<b -> 0 <= Z.rem a b < b.
Proof.
  intros; generalize (Zrem_lt_pos a b); lia.
Qed.

Theorem Zrem_lt_pos_neg a b : 0<=a -> b<0 -> 0 <= Z.rem a b < -b.
Proof.
  intros; generalize (Zrem_lt_pos a b); lia.
Qed.

Theorem Zrem_lt_neg_pos a b : a<=0 -> 0<b -> -b < Z.rem a b <= 0.
Proof.
  intros; generalize (Zrem_lt_neg a b); lia.
Qed.

Theorem Zrem_lt_neg_neg a b : a<=0 -> b<0 -> b < Z.rem a b <= 0.
Proof.
  intros; generalize (Zrem_lt_neg a b); lia.
Qed.


(** * Unicity results *)

Definition Remainder a b r :=
  (0 <= a /\ 0 <= r < Z.abs b) \/ (a <= 0 /\ -Z.abs b < r <= 0).

Definition Remainder_alt a b r :=
  Z.abs r < Z.abs b /\ 0 <= r * a.

Lemma Remainder_equiv : forall a b r,
 Remainder a b r <-> Remainder_alt a b r.
Proof.
  unfold Remainder, Remainder_alt; intuition.
  - lia.
  - lia.
  - rewrite <-(Z.mul_opp_opp). apply Z.mul_nonneg_nonneg; lia.
  - assert (0 <= Z.sgn r * Z.sgn a).
    { rewrite <-Z.sgn_mul, Z.sgn_nonneg; auto. }
    destruct r; simpl Z.sgn in *; lia.
Qed.

Theorem Zquot_mod_unique_full a b q r :
  Remainder a b r -> a = b*q + r -> q = a÷b /\ r = Z.rem a b.
Proof.
  destruct 1 as [(H,H0)|(H,H0)]; intros.
  apply Zdiv_mod_unique with b; auto.
  apply Zrem_lt_pos; auto.
  lia.
  rewrite <- H1; apply Z.quot_rem'.

  rewrite <- (Z.opp_involutive a).
  rewrite Zquot_opp_l, Zrem_opp_l.
  generalize (Zdiv_mod_unique b (-q) (-a÷b) (-r) (Z.rem (-a) b)).
  generalize (Zrem_lt_pos (-a) b).
  rewrite <-Z.quot_rem', Z.mul_opp_r, <-Z.opp_add_distr, <-H1.
  lia.
Qed.

Theorem Zquot_unique_full a b q r :
  Remainder a b r -> a = b*q + r -> q = a÷b.
Proof.
 intros; destruct (Zquot_mod_unique_full a b q r); auto.
Qed.

Theorem Zrem_unique_full a b q r :
  Remainder a b r -> a = b*q + r -> r = Z.rem a b.
Proof.
 intros; destruct (Zquot_mod_unique_full a b q r); auto.
Qed.

(** * Order results about Zrem and Zquot *)

(* Division of positive numbers is positive. *)

Lemma Z_quot_pos a b : 0 <= a -> 0 <= b -> 0 <= a÷b.
Proof. intros. zero_or_not b. apply Z.quot_pos; auto with zarith. Qed.

(** As soon as the divisor is greater or equal than 2,
    the division is strictly decreasing. *)

Lemma Z_quot_lt a b : 0 < a -> 2 <= b -> a÷b < a.
Proof. intros. apply Z.quot_lt; auto with zarith. Qed.

(** [<=] is compatible with a positive division. *)

Lemma Z_quot_monotone a b c : 0<=c -> a<=b -> a÷c <= b÷c.
Proof. intros. zero_or_not c. apply Z.quot_le_mono; auto with zarith. Qed.

(** With our choice of division, rounding of (a÷b) is always done toward 0: *)

Lemma Z_mult_quot_le a b : 0 <= a -> 0 <= b*(a÷b) <= a.
Proof. intros. zero_or_not b. apply Z.mul_quot_le; auto with zarith. Qed.

Lemma Z_mult_quot_ge a b : a <= 0 -> a <= b*(a÷b) <= 0.
Proof. intros. zero_or_not b. apply Z.mul_quot_ge; auto with zarith. Qed.

(** The previous inequalities between [b*(a÷b)] and [a] are exact
    iff the modulo is zero. *)

Lemma Z_quot_exact_full a b : a = b*(a÷b) <-> Z.rem a b = 0.
Proof. intros. zero_or_not b. intuition. apply Z.quot_exact; auto. Qed.

(** A modulo cannot grow beyond its starting point. *)

Theorem Zrem_le a b : 0 <= a -> 0 <= b -> Z.rem a b <= a.
Proof. intros. zero_or_not b. apply Z.rem_le; auto with zarith. Qed.

(** Some additional inequalities about Zdiv. *)

Theorem Zquot_le_upper_bound:
  forall a b q, 0 < b -> a <= q*b -> a÷b <= q.
Proof. intros a b q; rewrite Z.mul_comm; apply Z.quot_le_upper_bound. Qed.

Theorem Zquot_lt_upper_bound:
  forall a b q, 0 <= a -> 0 < b -> a < q*b -> a÷b < q.
Proof. intros a b q; rewrite Z.mul_comm; apply Z.quot_lt_upper_bound. Qed.

Theorem Zquot_le_lower_bound:
  forall a b q, 0 < b -> q*b <= a -> q <= a÷b.
Proof. intros a b q; rewrite Z.mul_comm; apply Z.quot_le_lower_bound. Qed.

Theorem Zquot_sgn: forall a b,
  0 <= Z.sgn (a÷b) * Z.sgn a * Z.sgn b.
Proof.
  destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith;
  unfold Z.quot; simpl; destruct N.pos_div_eucl; simpl; destruct n; simpl; auto with zarith.
Qed.

(** * Relations between usual operations and Zmod and Zdiv *)

(** First, a result that used to be always valid with Zdiv,
    but must be restricted here.
    For instance, now (9+(-5)*2) rem 2 = -1 <> 1 = 9 rem 2 *)

Lemma Z_rem_plus : forall a b c:Z,
 0 <= (a+b*c) * a ->
 Z.rem (a + b * c) c = Z.rem a c.
Proof. intros. zero_or_not c. apply Z.rem_add; auto with zarith. Qed.

Lemma Z_quot_plus : forall a b c:Z,
 0 <= (a+b*c) * a -> c<>0 ->
 (a + b * c) ÷ c = a ÷ c + b.
Proof. intros. apply Z.quot_add; auto with zarith. Qed.

Theorem Z_quot_plus_l: forall a b c : Z,
 0 <= (a*b+c)*c -> b<>0 ->
 b<>0 -> (a * b + c) ÷ b = a + c ÷ b.
Proof. intros. apply Z.quot_add_l; auto with zarith. Qed.

(** Cancellations. *)

Lemma Zquot_mult_cancel_r : forall a b c:Z,
 c<>0 -> (a*c)÷(b*c) = a÷b.
Proof. intros. zero_or_not b. apply Z.quot_mul_cancel_r; auto. Qed.

Lemma Zquot_mult_cancel_l : forall a b c:Z,
 c<>0 -> (c*a)÷(c*b) = a÷b.
Proof.
 intros. rewrite (Z.mul_comm c b). zero_or_not b.
 rewrite (Z.mul_comm b c). apply Z.quot_mul_cancel_l; auto.
Qed.

Lemma Zmult_rem_distr_l: forall a b c,
  Z.rem (c*a) (c*b) = c * (Z.rem a b).
Proof.
 intros. zero_or_not c. rewrite (Z.mul_comm c b). zero_or_not b.
 rewrite (Z.mul_comm b c). apply Z.mul_rem_distr_l; auto.
Qed.

Lemma Zmult_rem_distr_r: forall a b c,
  Z.rem (a*c) (b*c) = (Z.rem a b) * c.
Proof.
 intros. zero_or_not b. rewrite (Z.mul_comm b c). zero_or_not c.
 rewrite (Z.mul_comm c b). apply Z.mul_rem_distr_r; auto.
Qed.

(** Operations modulo. *)

Theorem Zrem_rem: forall a n, Z.rem (Z.rem a n) n = Z.rem a n.
Proof. intros. zero_or_not n. apply Z.rem_rem; auto. Qed.

Theorem Zmult_rem: forall a b n,
 Z.rem (a * b) n = Z.rem (Z.rem a n * Z.rem b n) n.
Proof. intros. zero_or_not n. apply Z.mul_rem; auto. Qed.

(** addition and modulo

  Generally speaking, unlike with Zdiv, we don't have
       (a+b) rem n = (a rem n + b rem n) rem n
  for any a and b.
  For instance, take (8 + (-10)) rem 3 = -2 whereas
  (8 rem 3 + (-10 rem 3)) rem 3 = 1. *)

Theorem Zplus_rem: forall a b n,
 0 <= a * b ->
 Z.rem (a + b) n = Z.rem (Z.rem a n + Z.rem b n) n.
Proof. intros. zero_or_not n. apply Z.add_rem; auto. Qed.

Lemma Zplus_rem_idemp_l: forall a b n,
 0 <= a * b ->
 Z.rem (Z.rem a n + b) n = Z.rem (a + b) n.
Proof. intros. zero_or_not n. apply Z.add_rem_idemp_l; auto. Qed.

Lemma Zplus_rem_idemp_r: forall a b n,
 0 <= a*b ->
 Z.rem (b + Z.rem a n) n = Z.rem (b + a) n.
Proof.
 intros. zero_or_not n. apply Z.add_rem_idemp_r; auto.
 rewrite Z.mul_comm; auto.
Qed.

Lemma Zmult_rem_idemp_l: forall a b n, Z.rem (Z.rem a n * b) n = Z.rem (a * b) n.
Proof. intros. zero_or_not n. apply Z.mul_rem_idemp_l; auto. Qed.

Lemma Zmult_rem_idemp_r: forall a b n, Z.rem (b * Z.rem a n) n = Z.rem (b * a) n.
Proof. intros. zero_or_not n. apply Z.mul_rem_idemp_r; auto. Qed.

(** Unlike with Zdiv, the following result is true without restrictions. *)

Lemma Zquot_Zquot : forall a b c, (a÷b)÷c = a÷(b*c).
Proof.
 intros. zero_or_not b. rewrite Z.mul_comm. zero_or_not c.
 rewrite Z.mul_comm. apply Z.quot_quot; auto.
Qed.

(** A last inequality: *)

Theorem Zquot_mult_le:
 forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a÷b) <= (c*a)÷b.
Proof. intros. zero_or_not b. apply Z.quot_mul_le; auto with zarith. Qed.

(** Z.rem is related to divisibility (see more in Znumtheory) *)

Lemma Zrem_divides : forall a b,
 Z.rem a b = 0 <-> exists c, a = b*c.
Proof.
 intros. zero_or_not b. firstorder.
 rewrite Z.rem_divide; trivial.
 split; intros (c,Hc); exists c; subst; auto with zarith.
Qed.

(** Particular case : dividing by 2 is related with parity *)

Lemma Zquot2_odd_remainder : forall a,
 Remainder a 2 (if Z.odd a then Z.sgn a else 0).
Proof.
 intros [ |p|p]. simpl.
 left. simpl. auto with zarith.
 left. destruct p; simpl; auto with zarith.
 right. destruct p; simpl; split; now auto with zarith.
Qed.

Lemma Zrem_odd : forall a, Z.rem a 2 = if Z.odd a then Z.sgn a else 0.
Proof.
 intros. symmetry.
 apply Zrem_unique_full with (Z.quot2 a).
 apply Zquot2_odd_remainder.
 apply Zquot2_odd_eqn.
Qed.

Lemma Zrem_even : forall a, Z.rem a 2 = if Z.even a then 0 else Z.sgn a.
Proof.
 intros a. rewrite Zrem_odd, Zodd_even_bool. now destruct Z.even.
Qed.

Lemma Zeven_rem : forall a, Z.even a = Z.eqb (Z.rem a 2) 0.
Proof.
 intros a. rewrite Zrem_even.
 destruct a as [ |p|p]; trivial; now destruct p.
Qed.

Lemma Zodd_rem : forall a, Z.odd a = negb (Z.eqb (Z.rem a 2) 0).
Proof.
 intros a. rewrite Zrem_odd.
 destruct a as [ |p|p]; trivial; now destruct p.
Qed.

(** * Interaction with "historic" Zdiv *)

(** They agree at least on positive numbers: *)

Theorem Zquotrem_Zdiv_eucl_pos : forall a b:Z, 0 <= a -> 0 < b ->
  a÷b = a/b /\ Z.rem a b = a mod b.
Proof.
  intros.
  apply Zdiv_mod_unique with b.
  apply Zrem_lt_pos; auto with zarith.
  rewrite Z.abs_eq; auto with *; apply Z_mod_lt; auto with *.
  rewrite <- Z_div_mod_eq; auto with *.
  symmetry; apply Z.quot_rem; auto with *.
Qed.

Theorem Zquot_Zdiv_pos : forall a b, 0 <= a -> 0 <= b ->
  a÷b = a/b.
Proof.
 intros a b Ha Hb. Z.le_elim Hb.
 - generalize (Zquotrem_Zdiv_eucl_pos a b Ha Hb); intuition.
 - subst; now rewrite Zquot_0_r, Zdiv_0_r.
Qed.

Theorem Zrem_Zmod_pos : forall a b, 0 <= a -> 0 < b ->
  Z.rem a b = a mod b.
Proof.
 intros a b Ha Hb; generalize (Zquotrem_Zdiv_eucl_pos a b Ha Hb);
 intuition.
Qed.

(** Modulos are null at the same places *)

Theorem Zrem_Zmod_zero : forall a b, b<>0 ->
 (Z.rem a b = 0 <-> a mod b = 0).
Proof.
 intros.
 rewrite Zrem_divides, Zmod_divides; intuition.
Qed.
