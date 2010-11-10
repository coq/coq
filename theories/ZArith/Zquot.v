(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos BinNat Nnat ZArith_base ROmega ZArithRing Morphisms Zdiv.
Require Export Ndiv_def Zdiv_def.
Require ZBinary ZDivTrunc.

Local Open Scope Z_scope.

(** This file provides results about the Round-Toward-Zero Euclidean
  division [Zquotrem], whose projections are [Zquot] and [Zrem].
  Definition of this division can be found in file [Zdiv_def].

  This division and the one defined in Zdiv agree only on positive
  numbers. Otherwise, Zdiv performs Round-Toward-Bottom (a.k.a Floor).

  The current approach is compatible with the division of usual
  programming languages such as Ocaml. In addition, it has nicer
  properties with respect to opposite and other usual operations.
*)

(** * Relation between division on N and on Z. *)

Lemma Ndiv_Zquot : forall a b:N,
  Z_of_N (a/b) = (Z_of_N a ÷ Z_of_N b).
Proof.
  intros.
  destruct a; destruct b; simpl; auto.
  unfold Ndiv, Zquot; simpl; destruct Pdiv_eucl; auto.
Qed.

Lemma Nmod_Zrem : forall a b:N,
  Z_of_N (a mod b) = (Z_of_N a) rem (Z_of_N b).
Proof.
  intros.
  destruct a; destruct b; simpl; auto.
  unfold Nmod, Zrem; simpl; destruct Pdiv_eucl; auto.
Qed.

(** * Characterization of this euclidean division. *)

(** First, the usual equation [a=q*b+r]. Notice that [a mod 0]
   has been chosen to be [a], so this equation holds even for [b=0].
*)

Notation Z_quot_rem_eq := Z_quot_rem_eq (only parsing).

(** Then, the inequalities constraining the remainder:
    The remainder is bounded by the divisor, in term of absolute values *)

Theorem Zrem_lt : forall a b:Z, b<>0 ->
  Zabs (a rem b) < Zabs b.
Proof.
  destruct b as [ |b|b]; intro H; try solve [elim H;auto];
  destruct a as [ |a|a]; try solve [compute;auto]; unfold Zrem, Zquotrem;
  generalize (Pdiv_eucl_remainder a b); destruct Pdiv_eucl; simpl;
  try rewrite Zabs_Zopp; rewrite Zabs_eq; auto using Z_of_N_le_0;
  intros LT; apply (Z_of_N_lt _ _ LT).
Qed.

(** The sign of the remainder is the one of [a]. Due to the possible
   nullity of [a], a general result is to be stated in the following form:
*)

Theorem Zrem_sgn : forall a b:Z,
  0 <= Zsgn (a rem b) * Zsgn a.
Proof.
  destruct b as [ |b|b]; destruct a as [ |a|a]; simpl; auto with zarith;
  unfold Zrem, Zquotrem; destruct Pdiv_eucl;
  simpl; destruct n0; simpl; auto with zarith.
Qed.

(** This can also be said in a simplier way: *)

Theorem Zsgn_pos_iff : forall z, 0 <= Zsgn z <-> 0 <= z.
Proof.
 destruct z; simpl; intuition auto with zarith.
Qed.

Theorem Zrem_sgn2 : forall a b:Z,
  0 <= (a rem b) * a.
Proof.
  intros; rewrite <-Zsgn_pos_iff, Zsgn_Zmult; apply Zrem_sgn.
Qed.

(** Reformulation of [Zquot_lt] and [Zrem_sgn] in 2
  then 4 particular cases. *)

Theorem Zrem_lt_pos : forall a b:Z, 0<=a -> b<>0 ->
  0 <= a rem b < Zabs b.
Proof.
  intros.
  assert (0 <= a rem b).
   generalize (Zrem_sgn a b).
   destruct (Zle_lt_or_eq 0 a H).
   rewrite <- Zsgn_pos in H1; rewrite H1; romega with *.
   subst a; simpl; auto.
  generalize (Zrem_lt a b H0); romega with *.
Qed.

Theorem Zrem_lt_neg : forall a b:Z, a<=0 -> b<>0 ->
  -Zabs b < a rem b <= 0.
Proof.
  intros.
  assert (a rem b <= 0).
   generalize (Zrem_sgn a b).
   destruct (Zle_lt_or_eq a 0 H).
   rewrite <- Zsgn_neg in H1; rewrite H1; romega with *.
   subst a; simpl; auto.
  generalize (Zrem_lt a b H0); romega with *.
Qed.

Theorem Zrem_lt_pos_pos : forall a b:Z, 0<=a -> 0<b -> 0 <= a rem b < b.
Proof.
  intros; generalize (Zrem_lt_pos a b); romega with *.
Qed.

Theorem Zrem_lt_pos_neg : forall a b:Z, 0<=a -> b<0 -> 0 <= a rem b < -b.
Proof.
  intros; generalize (Zrem_lt_pos a b); romega with *.
Qed.

Theorem Zrem_lt_neg_pos : forall a b:Z, a<=0 -> 0<b -> -b < a rem b <= 0.
Proof.
  intros; generalize (Zrem_lt_neg a b); romega with *.
Qed.

Theorem Zrem_lt_neg_neg : forall a b:Z, a<=0 -> b<0 -> b < a rem b <= 0.
Proof.
  intros; generalize (Zrem_lt_neg a b); romega with *.
Qed.

(** * Division and Opposite *)

(* The precise equalities that are invalid with "historic" Zdiv. *)

Theorem Zquot_opp_l : forall a b:Z, (-a)÷b = -(a÷b).
Proof.
 destruct a; destruct b; simpl; auto;
  unfold Zquot, Zquotrem; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem Zquot_opp_r : forall a b:Z, a÷(-b) = -(a÷b).
Proof.
 destruct a; destruct b; simpl; auto;
  unfold Zquot, Zquotrem; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem Zrem_opp_l : forall a b:Z, (-a) rem b = -(a rem b).
Proof.
 destruct a; destruct b; simpl; auto;
  unfold Zrem, Zquotrem; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem Zrem_opp_r : forall a b:Z, a rem (-b) = a rem b.
Proof.
 destruct a; destruct b; simpl; auto;
  unfold Zrem, Zquotrem; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem Zquot_opp_opp : forall a b:Z, (-a)÷(-b) = a÷b.
Proof.
 destruct a; destruct b; simpl; auto;
  unfold Zquot, Zquotrem; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem Zrem_opp_opp : forall a b:Z, (-a) rem (-b) = -(a rem b).
Proof.
 destruct a; destruct b; simpl; auto;
  unfold Zrem, Zquotrem; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

(** * Unicity results *)

Definition Remainder a b r :=
  (0 <= a /\ 0 <= r < Zabs b) \/ (a <= 0 /\ -Zabs b < r <= 0).

Definition Remainder_alt a b r :=
  Zabs r < Zabs b /\ 0 <= r * a.

Lemma Remainder_equiv : forall a b r,
 Remainder a b r <-> Remainder_alt a b r.
Proof.
  unfold Remainder, Remainder_alt; intuition.
  romega with *.
  romega with *.
  rewrite <-(Zmult_opp_opp).
  apply Zmult_le_0_compat; romega.
  assert (0 <= Zsgn r * Zsgn a) by (rewrite <-Zsgn_Zmult, Zsgn_pos_iff; auto).
  destruct r; simpl Zsgn in *; romega with *.
Qed.

Theorem Zquot_mod_unique_full:
 forall a b q r, Remainder a b r ->
   a = b*q + r -> q = a÷b /\ r = a rem b.
Proof.
  destruct 1 as [(H,H0)|(H,H0)]; intros.
  apply Zdiv_mod_unique with b; auto.
  apply Zrem_lt_pos; auto.
  romega with *.
  rewrite <- H1; apply Z_quot_rem_eq.

  rewrite <- (Zopp_involutive a).
  rewrite Zquot_opp_l, Zrem_opp_l.
  generalize (Zdiv_mod_unique b (-q) (-a÷b) (-r) (-a rem b)).
  generalize (Zrem_lt_pos (-a) b).
  rewrite <-Z_quot_rem_eq, <-Zopp_mult_distr_r, <-Zopp_plus_distr, <-H1.
  romega with *.
Qed.

Theorem Zquot_unique_full:
 forall a b q r, Remainder a b r ->
  a = b*q + r -> q = a÷b.
Proof.
 intros; destruct (Zquot_mod_unique_full a b q r); auto.
Qed.

Theorem Zquot_unique:
 forall a b q r, 0 <= a -> 0 <= r < b ->
   a = b*q + r -> q = a÷b.
Proof. exact Z.quot_unique. Qed.

Theorem Zrem_unique_full:
 forall a b q r, Remainder a b r ->
  a = b*q + r -> r = a rem b.
Proof.
 intros; destruct (Zquot_mod_unique_full a b q r); auto.
Qed.

Theorem Zrem_unique:
 forall a b q r, 0 <= a -> 0 <= r < b ->
   a = b*q + r -> r = a rem b.
Proof. exact Z.rem_unique. Qed.

(** * Basic values of divisions and modulo. *)

Lemma Zrem_0_l: forall a, 0 rem a = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zrem_0_r: forall a, a rem 0 = a.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zquot_0_l: forall a, 0÷a = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zquot_0_r: forall a, a÷0 = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zrem_1_r: forall a, a rem 1 = 0.
Proof. exact Z.rem_1_r. Qed.

Lemma Zquot_1_r: forall a, a÷1 = a.
Proof. exact Z.quot_1_r. Qed.

Hint Resolve Zrem_0_l Zrem_0_r Zquot_0_l Zquot_0_r Zquot_1_r Zrem_1_r
 : zarith.

Lemma Zquot_1_l: forall a, 1 < a -> 1÷a = 0.
Proof. exact Z.quot_1_l. Qed.

Lemma Zrem_1_l: forall a, 1 < a ->  1 rem a = 1.
Proof. exact Z.rem_1_l. Qed.

Lemma Z_quot_same : forall a:Z, a<>0 -> a÷a = 1.
Proof. exact Z.quot_same. Qed.

Ltac zero_or_not a :=
  destruct (Z_eq_dec a 0);
  [subst; rewrite ?Zrem_0_l, ?Zquot_0_l, ?Zrem_0_r, ?Zquot_0_r;
   auto with zarith|].

Lemma Z_rem_same : forall a, a rem a = 0.
Proof. intros. zero_or_not a. apply Z.rem_same; auto. Qed.

Lemma Z_rem_mult : forall a b, (a*b) rem b = 0.
Proof. intros. zero_or_not b. apply Z.rem_mul; auto. Qed.

Lemma Z_quot_mult : forall a b:Z, b <> 0 -> (a*b)÷b = a.
Proof. exact Z.quot_mul. Qed.

(** * Order results about Zrem and Zquot *)

(* Division of positive numbers is positive. *)

Lemma Z_quot_pos: forall a b, 0 <= a -> 0 <= b -> 0 <= a÷b.
Proof. intros. zero_or_not b. apply Z.quot_pos; auto with zarith. Qed.

(** As soon as the divisor is greater or equal than 2,
    the division is strictly decreasing. *)

Lemma Z_quot_lt : forall a b:Z, 0 < a -> 2 <= b -> a÷b < a.
Proof. intros. apply Z.quot_lt; auto with zarith. Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem Zquot_small: forall a b, 0 <= a < b -> a÷b = 0.
Proof. exact Z.quot_small. Qed.

(** Same situation, in term of modulo: *)

Theorem Zrem_small: forall a n, 0 <= a < n -> a rem n = a.
Proof. exact Z.rem_small. Qed.

(** [Zge] is compatible with a positive division. *)

Lemma Z_quot_monotone : forall a b c, 0<=c -> a<=b -> a÷c <= b÷c.
Proof. intros. zero_or_not c. apply Z.quot_le_mono; auto with zarith. Qed.

(** With our choice of division, rounding of (a÷b) is always done toward zero: *)

Lemma Z_mult_quot_le : forall a b:Z, 0 <= a -> 0 <= b*(a÷b) <= a.
Proof. intros. zero_or_not b. apply Z.mul_quot_le; auto with zarith. Qed.

Lemma Z_mult_quot_ge : forall a b:Z, a <= 0 -> a <= b*(a÷b) <= 0.
Proof. intros. zero_or_not b. apply Z.mul_quot_ge; auto with zarith. Qed.

(** The previous inequalities between [b*(a÷b)] and [a] are exact
    iff the modulo is zero. *)

Lemma Z_quot_exact_full : forall a b:Z, a = b*(a÷b) <-> a rem b = 0.
Proof. intros. zero_or_not b. intuition. apply Z.quot_exact; auto. Qed.

(** A modulo cannot grow beyond its starting point. *)

Theorem Zrem_le: forall a b, 0 <= a -> 0 <= b -> a rem b <= a.
Proof. intros. zero_or_not b. apply Z.rem_le; auto with zarith. Qed.

(** Some additionnal inequalities about Zdiv. *)

Theorem Zquot_le_upper_bound:
  forall a b q, 0 < b -> a <= q*b -> a÷b <= q.
Proof. intros a b q; rewrite Zmult_comm; apply Z.quot_le_upper_bound. Qed.

Theorem Zquot_lt_upper_bound:
  forall a b q, 0 <= a -> 0 < b -> a < q*b -> a÷b < q.
Proof. intros a b q; rewrite Zmult_comm; apply Z.quot_lt_upper_bound. Qed.

Theorem Zquot_le_lower_bound:
  forall a b q, 0 < b -> q*b <= a -> q <= a÷b.
Proof. intros a b q; rewrite Zmult_comm; apply Z.quot_le_lower_bound. Qed.

Theorem Zquot_sgn: forall a b,
  0 <= Zsgn (a÷b) * Zsgn a * Zsgn b.
Proof.
  destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith;
  unfold Zquot; simpl; destruct Pdiv_eucl; simpl; destruct n; simpl; auto with zarith.
Qed.

(** * Relations between usual operations and Zmod and Zdiv *)

(** First, a result that used to be always valid with Zdiv,
    but must be restricted here.
    For instance, now (9+(-5)*2) rem 2 = -1 <> 1 = 9 rem 2 *)

Lemma Z_rem_plus : forall a b c:Z,
 0 <= (a+b*c) * a ->
 (a + b * c) rem c = a rem c.
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
 intros. rewrite (Zmult_comm c b). zero_or_not b.
 rewrite (Zmult_comm b c). apply Z.quot_mul_cancel_l; auto.
Qed.

Lemma Zmult_rem_distr_l: forall a b c,
  (c*a) rem (c*b) = c * (a rem b).
Proof.
 intros. zero_or_not c. rewrite (Zmult_comm c b). zero_or_not b.
 rewrite (Zmult_comm b c). apply Z.mul_rem_distr_l; auto.
Qed.

Lemma Zmult_rem_distr_r: forall a b c,
  (a*c) rem (b*c) = (a rem b) * c.
Proof.
 intros. zero_or_not b. rewrite (Zmult_comm b c). zero_or_not c.
 rewrite (Zmult_comm c b). apply Z.mul_rem_distr_r; auto.
Qed.

(** Operations modulo. *)

Theorem Zrem_rem: forall a n, (a rem n) rem n = a rem n.
Proof. intros. zero_or_not n. apply Z.rem_rem; auto. Qed.

Theorem Zmult_rem: forall a b n,
 (a * b) rem n = ((a rem n) * (b rem n)) rem n.
Proof. intros. zero_or_not n. apply Z.mul_rem; auto. Qed.

(** addition and modulo

  Generally speaking, unlike with Zdiv, we don't have
       (a+b) rem n = (a rem n + b rem n) rem n
  for any a and b.
  For instance, take (8 + (-10)) rem 3 = -2 whereas
  (8 rem 3 + (-10 rem 3)) rem 3 = 1. *)

Theorem Zplus_rem: forall a b n,
 0 <= a * b ->
 (a + b) rem n = (a rem n + b rem n) rem n.
Proof. intros. zero_or_not n. apply Z.add_rem; auto. Qed.

Lemma Zplus_rem_idemp_l: forall a b n,
 0 <= a * b ->
 (a rem n + b) rem n = (a + b) rem n.
Proof. intros. zero_or_not n. apply Z.add_rem_idemp_l; auto. Qed.

Lemma Zplus_rem_idemp_r: forall a b n,
 0 <= a*b ->
 (b + a rem n) rem n = (b + a) rem n.
Proof.
 intros. zero_or_not n. apply Z.add_rem_idemp_r; auto.
 rewrite Zmult_comm; auto. Qed.

Lemma Zmult_rem_idemp_l: forall a b n, (a rem n * b) rem n = (a * b) rem n.
Proof. intros. zero_or_not n. apply Z.mul_rem_idemp_l; auto. Qed.

Lemma Zmult_rem_idemp_r: forall a b n, (b * (a rem n)) rem n = (b * a) rem n.
Proof. intros. zero_or_not n. apply Z.mul_rem_idemp_r; auto. Qed.

(** Unlike with Zdiv, the following result is true without restrictions. *)

Lemma Zquot_Zquot : forall a b c, (a÷b)÷c = a÷(b*c).
Proof.
 intros. zero_or_not b. rewrite Zmult_comm. zero_or_not c.
 rewrite Zmult_comm. apply Z.quot_quot; auto.
Qed.

(** A last inequality: *)

Theorem Zquot_mult_le:
 forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a÷b) <= (c*a)÷b.
Proof. intros. zero_or_not b. apply Z.quot_mul_le; auto with zarith. Qed.

(** Zrem is related to divisibility (see more in Znumtheory) *)

Lemma Zrem_divides : forall a b,
 a rem b = 0 <-> exists c, a = b*c.
Proof.
 intros. zero_or_not b. firstorder.
 rewrite Z.rem_divide; trivial. split; intros (c,Hc); exists c; auto.
Qed.

(** * Interaction with "historic" Zdiv *)

(** They agree at least on positive numbers: *)

Theorem Zquotrem_Zdiv_eucl_pos : forall a b:Z, 0 <= a -> 0 < b ->
  a÷b = a/b /\ a rem b = a mod b.
Proof.
  intros.
  apply Zdiv_mod_unique with b.
  apply Zrem_lt_pos; auto with zarith.
  rewrite Zabs_eq; auto with *; apply Z_mod_lt; auto with *.
  rewrite <- Z_div_mod_eq; auto with *.
  symmetry; apply Z_quot_rem_eq; auto with *.
Qed.

Theorem Zquot_Zdiv_pos : forall a b, 0 <= a -> 0 <= b ->
  a÷b = a/b.
Proof.
 intros a b Ha Hb.
 destruct (Zle_lt_or_eq _ _ Hb).
 generalize (Zquotrem_Zdiv_eucl_pos a b Ha H); intuition.
 subst; rewrite Zquot_0_r, Zdiv_0_r; reflexivity.
Qed.

Theorem Zrem_Zmod_pos : forall a b, 0 <= a -> 0 < b ->
  a rem b = a mod b.
Proof.
 intros a b Ha Hb; generalize (Zquotrem_Zdiv_eucl_pos a b Ha Hb);
 intuition.
Qed.

(** Modulos are null at the same places *)

Theorem Zrem_Zmod_zero : forall a b, b<>0 ->
 (a rem b = 0 <-> a mod b = 0).
Proof.
 intros.
 rewrite Zrem_divides, Zmod_divides; intuition.
Qed.
