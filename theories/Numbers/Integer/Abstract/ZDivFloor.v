(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZAxioms ZMulOrder ZSgnAbs NZDiv.

(** * Euclidean Division for integers (Floor convention)

    We use here the convention known as Floor, or Round-Toward-Bottom,
    where [a/b] is the closest integer below the exact fraction.
    It can be summarized by:

    [a = bq+r /\ 0 <= |r| < |b| /\ Sign(r) = Sign(b)]

    This is the convention followed historically by [Z.div] in Coq, and
    corresponds to convention "F" in the following paper:

    R. Boute, "The Euclidean definition of the functions div and mod",
    ACM Transactions on Programming Languages and Systems,
    Vol. 14, No.2, pp. 127-144, April 1992.

    See files [ZDivTrunc] and [ZDivEucl] for others conventions.
*)

Module Type ZDivProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZSgnAbsProp A B).

(** We benefit from what already exists for NZ *)
Module Import Private_NZDiv := Nop <+ NZDivProp A A B.

(** Another formulation of the main equation *)

Lemma mod_eq :
 forall a b, b~=0 -> a mod b == a - b*(a/b).
Proof.
intros.
rewrite <- add_move_l.
symmetry. now apply div_mod.
Qed.

(** We have a general bound for absolute values *)

Lemma mod_bound_abs :
 forall a b, b~=0 -> abs (a mod b) < abs b.
Proof.
intros.
destruct (abs_spec b) as [(LE,EQ)|(LE,EQ)]; rewrite EQ.
destruct (mod_pos_bound a b). order. now rewrite abs_eq.
destruct (mod_neg_bound a b). order. rewrite abs_neq; trivial.
now rewrite <- opp_lt_mono.
Qed.

(** Uniqueness theorems *)

Theorem div_mod_unique : forall b q1 q2 r1 r2 : t,
  (0<=r1<b \/ b<r1<=0) -> (0<=r2<b \/ b<r2<=0) ->
  b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof.
intros b q1 q2 r1 r2 Hr1 Hr2 EQ.
destruct Hr1; destruct Hr2; try (intuition; order).
apply div_mod_unique with b; trivial.
rewrite <- (opp_inj_wd r1 r2).
apply div_mod_unique with (-b); trivial.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; tauto.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; tauto.
now rewrite 2 mul_opp_l, <- 2 opp_add_distr, opp_inj_wd.
Qed.

Theorem div_unique:
 forall a b q r, (0<=r<b \/ b<r<=0) -> a == b*q + r -> q == a/b.
Proof.
intros a b q r Hr EQ.
assert (Hb : b~=0) by (destruct Hr; intuition; order).
destruct (div_mod_unique b q (a/b) r (a mod b)); trivial.
destruct Hr; [left; apply mod_pos_bound|right; apply mod_neg_bound];
 intuition order.
now rewrite <- div_mod.
Qed.

Theorem div_unique_pos:
 forall a b q r, 0<=r<b -> a == b*q + r -> q == a/b.
Proof. intros; apply div_unique with r; auto. Qed.

Theorem div_unique_neg:
 forall a b q r, b<r<=0 -> a == b*q + r -> q == a/b.
Proof. intros; apply div_unique with r; auto. Qed.

Theorem mod_unique:
 forall a b q r, (0<=r<b \/ b<r<=0) -> a == b*q + r -> r == a mod b.
Proof.
intros a b q r Hr EQ.
assert (Hb : b~=0) by (destruct Hr; intuition; order).
destruct (div_mod_unique b q (a/b) r (a mod b)); trivial.
destruct Hr; [left; apply mod_pos_bound|right; apply mod_neg_bound];
 intuition order.
now rewrite <- div_mod.
Qed.

Theorem mod_unique_pos:
 forall a b q r, 0<=r<b -> a == b*q + r -> r == a mod b.
Proof. intros; apply mod_unique with q; auto. Qed.

Theorem mod_unique_neg:
 forall a b q r, b<r<=0 -> a == b*q + r -> r == a mod b.
Proof. intros; apply mod_unique with q; auto. Qed.

(** Sign rules *)

Ltac pos_or_neg a :=
 let LT := fresh "LT" in
 let LE := fresh "LE" in
 destruct (le_gt_cases 0 a) as [LE|LT]; [|rewrite <- opp_pos_neg in LT].

Fact mod_bound_or : forall a b, b~=0 -> 0<=a mod b<b \/ b<a mod b<=0.
Proof.
intros.
destruct (lt_ge_cases 0 b); [left|right].
 apply mod_pos_bound; trivial. apply mod_neg_bound; order.
Qed.

Fact opp_mod_bound_or : forall a b, b~=0 ->
 0 <= -(a mod b) < -b \/ -b < -(a mod b) <= 0.
Proof.
intros.
destruct (lt_ge_cases 0 b); [right|left].
rewrite <- opp_lt_mono, opp_nonpos_nonneg.
 destruct (mod_pos_bound a b); intuition; order.
rewrite <- opp_lt_mono, opp_nonneg_nonpos.
 destruct (mod_neg_bound a b); intuition; order.
Qed.

Lemma div_opp_opp : forall a b, b~=0 -> -a/-b == a/b.
Proof.
intros. symmetry. apply div_unique with (- (a mod b)).
now apply opp_mod_bound_or.
rewrite mul_opp_l, <- opp_add_distr, <- div_mod; order.
Qed.

Lemma mod_opp_opp : forall a b, b~=0 -> (-a) mod (-b) == - (a mod b).
Proof.
intros. symmetry. apply mod_unique with (a/b).
now apply opp_mod_bound_or.
rewrite mul_opp_l, <- opp_add_distr, <- div_mod; order.
Qed.

(** With the current conventions, the other sign rules are rather complex. *)

Lemma div_opp_l_z :
 forall a b, b~=0 -> a mod b == 0 -> (-a)/b == -(a/b).
Proof.
intros a b Hb H. symmetry. apply div_unique with 0.
destruct (lt_ge_cases 0 b); [left|right]; intuition; order.
rewrite <- opp_0, <- H.
rewrite mul_opp_r, <- opp_add_distr, <- div_mod; order.
Qed.

Lemma div_opp_l_nz :
 forall a b, b~=0 -> a mod b ~= 0 -> (-a)/b == -(a/b)-1.
Proof.
intros a b Hb H. symmetry. apply div_unique with (b - a mod b).
destruct (lt_ge_cases 0 b); [left|right].
rewrite le_0_sub. rewrite <- (sub_0_r b) at 5. rewrite <- sub_lt_mono_l.
destruct (mod_pos_bound a b); intuition; order.
rewrite le_sub_0. rewrite <- (sub_0_r b) at 1. rewrite <- sub_lt_mono_l.
destruct (mod_neg_bound a b); intuition; order.
rewrite <- (add_opp_r b), mul_sub_distr_l, mul_1_r, sub_add_simpl_r_l.
rewrite mul_opp_r, <-opp_add_distr, <-div_mod; order.
Qed.

Lemma mod_opp_l_z :
 forall a b, b~=0 -> a mod b == 0 -> (-a) mod b == 0.
Proof.
intros a b Hb H. symmetry. apply mod_unique with (-(a/b)).
destruct (lt_ge_cases 0 b); [left|right]; intuition; order.
rewrite <- opp_0, <- H.
rewrite mul_opp_r, <- opp_add_distr, <- div_mod; order.
Qed.

Lemma mod_opp_l_nz :
 forall a b, b~=0 -> a mod b ~= 0 -> (-a) mod b == b - a mod b.
Proof.
intros a b Hb H. symmetry. apply mod_unique with (-(a/b)-1).
destruct (lt_ge_cases 0 b); [left|right].
rewrite le_0_sub. rewrite <- (sub_0_r b) at 5. rewrite <- sub_lt_mono_l.
destruct (mod_pos_bound a b); intuition; order.
rewrite le_sub_0. rewrite <- (sub_0_r b) at 1. rewrite <- sub_lt_mono_l.
destruct (mod_neg_bound a b); intuition; order.
rewrite <- (add_opp_r b), mul_sub_distr_l, mul_1_r, sub_add_simpl_r_l.
rewrite mul_opp_r, <-opp_add_distr, <-div_mod; order.
Qed.

Lemma div_opp_r_z :
 forall a b, b~=0 -> a mod b == 0 -> a/(-b) == -(a/b).
Proof.
intros. rewrite <- (opp_involutive a) at 1.
rewrite div_opp_opp; auto using div_opp_l_z.
Qed.

Lemma div_opp_r_nz :
 forall a b, b~=0 -> a mod b ~= 0 -> a/(-b) == -(a/b)-1.
Proof.
intros. rewrite <- (opp_involutive a) at 1.
rewrite div_opp_opp; auto using div_opp_l_nz.
Qed.

Lemma mod_opp_r_z :
 forall a b, b~=0 -> a mod b == 0 -> a mod (-b) == 0.
Proof.
intros. rewrite <- (opp_involutive a) at 1.
now rewrite mod_opp_opp, mod_opp_l_z, opp_0.
Qed.

Lemma mod_opp_r_nz :
 forall a b, b~=0 -> a mod b ~= 0 -> a mod (-b) == (a mod b) - b.
Proof.
intros. rewrite <- (opp_involutive a) at 1.
rewrite mod_opp_opp, mod_opp_l_nz by trivial.
now rewrite opp_sub_distr, add_comm, add_opp_r.
Qed.

(** The sign of [a mod b] is the one of [b] (when it isn't null) *)

Lemma mod_sign_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 sgn (a mod b) == sgn b.
Proof.
intros a b Hb H. destruct (lt_ge_cases 0 b) as [Hb'|Hb'].
destruct (mod_pos_bound a b Hb'). rewrite 2 sgn_pos; order.
destruct (mod_neg_bound a b). order. rewrite 2 sgn_neg; order.
Qed.

Lemma mod_sign : forall a b, b~=0 -> sgn (a mod b) ~= -sgn b.
Proof.
intros a b Hb H.
destruct (eq_decidable (a mod b) 0) as [EQ|NEQ].
apply Hb, sgn_null_iff, opp_inj. now rewrite <- H, opp_0, EQ, sgn_0.
apply Hb, sgn_null_iff. apply eq_mul_0_l with 2; try order'. nzsimpl'.
apply add_move_0_l. rewrite <- H. symmetry. now apply mod_sign_nz.
Qed.

Lemma mod_sign_mul : forall a b, b~=0 -> 0 <= (a mod b) * b.
Proof.
intros. destruct (lt_ge_cases 0 b).
apply mul_nonneg_nonneg; destruct (mod_pos_bound a b); order.
apply mul_nonpos_nonpos; destruct (mod_neg_bound a b); order.
Qed.

(** A division by itself returns 1 *)

Lemma div_same : forall a, a~=0 -> a/a == 1.
Proof.
intros. pos_or_neg a. apply div_same; order.
rewrite <- div_opp_opp by trivial. now apply div_same.
Qed.

Lemma mod_same : forall a, a~=0 -> a mod a == 0.
Proof.
intros. rewrite mod_eq, div_same by trivial. nzsimpl. apply sub_diag.
Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem div_small: forall a b, 0<=a<b -> a/b == 0.
Proof. exact div_small. Qed.

(** Same situation, in term of modulo: *)

Theorem mod_small: forall a b, 0<=a<b -> a mod b == a.
Proof. exact mod_small. Qed.

(** * Basic values of divisions and modulo. *)

Lemma div_0_l: forall a, a~=0 -> 0/a == 0.
Proof.
intros. pos_or_neg a. apply div_0_l; order.
rewrite <- div_opp_opp, opp_0 by trivial. now apply div_0_l.
Qed.

Lemma mod_0_l: forall a, a~=0 -> 0 mod a == 0.
Proof.
intros; rewrite mod_eq, div_0_l; now nzsimpl.
Qed.

Lemma div_1_r: forall a, a/1 == a.
Proof.
intros. symmetry. apply div_unique with 0. left. split; order || apply lt_0_1.
now nzsimpl.
Qed.

Lemma mod_1_r: forall a, a mod 1 == 0.
Proof.
intros. rewrite mod_eq, div_1_r; nzsimpl; auto using sub_diag.
intro EQ; symmetry in EQ; revert EQ; apply lt_neq; apply lt_0_1.
Qed.

Lemma div_1_l: forall a, 1<a -> 1/a == 0.
Proof. exact div_1_l. Qed.

Lemma mod_1_l: forall a, 1<a -> 1 mod a == 1.
Proof. exact mod_1_l. Qed.

Lemma div_mul : forall a b, b~=0 -> (a*b)/b == a.
Proof.
intros. symmetry. apply div_unique with 0.
destruct (lt_ge_cases 0 b); [left|right]; split; order.
nzsimpl; apply mul_comm.
Qed.

Lemma mod_mul : forall a b, b~=0 -> (a*b) mod b == 0.
Proof.
intros. rewrite mod_eq, div_mul by trivial. rewrite mul_comm; apply sub_diag.
Qed.

Theorem div_unique_exact a b q: b~=0 -> a == b*q -> q == a/b.
Proof.
 intros Hb H. rewrite H, mul_comm. symmetry. now apply div_mul.
Qed.

(** * Order results about mod and div *)

(** A modulo cannot grow beyond its starting point. *)

Theorem mod_le: forall a b, 0<=a -> 0<b -> a mod b <= a.
Proof. exact mod_le. Qed.

Theorem div_pos : forall a b, 0<=a -> 0<b -> 0<= a/b.
Proof. exact div_pos. Qed.

Lemma div_str_pos : forall a b, 0<b<=a -> 0 < a/b.
Proof. exact div_str_pos. Qed.

Lemma div_small_iff : forall a b, b~=0 -> (a/b==0 <-> 0<=a<b \/ b<a<=0).
Proof.
intros a b Hb.
split.
intros EQ.
rewrite (div_mod a b Hb), EQ; nzsimpl.
now apply mod_bound_or.
destruct 1. now apply div_small.
rewrite <- div_opp_opp by trivial. apply div_small; trivial.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; tauto.
Qed.

Lemma mod_small_iff : forall a b, b~=0 -> (a mod b == a <-> 0<=a<b \/ b<a<=0).
Proof.
intros.
rewrite <- div_small_iff, mod_eq by trivial.
rewrite sub_move_r, <- (add_0_r a) at 1. rewrite add_cancel_l.
rewrite eq_sym_iff, eq_mul_0. tauto.
Qed.

(** As soon as the divisor is strictly greater than 1,
    the division is strictly decreasing. *)

Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof. exact div_lt. Qed.

(** [le] is compatible with a positive division. *)

Lemma div_le_mono : forall a b c, 0<c -> a<=b -> a/c <= b/c.
Proof.
intros a b c Hc Hab.
rewrite lt_eq_cases in Hab. destruct Hab as [LT|EQ];
 [|rewrite EQ; order].
rewrite <- lt_succ_r.
rewrite (mul_lt_mono_pos_l c) by order.
nzsimpl.
rewrite (add_lt_mono_r _ _ (a mod c)).
rewrite <- div_mod by order.
apply lt_le_trans with b; trivial.
rewrite (div_mod b c) at 1 by order.
rewrite <- add_assoc, <- add_le_mono_l.
apply le_trans with (c+0).
nzsimpl; destruct (mod_pos_bound b c); order.
rewrite <- add_le_mono_l. destruct (mod_pos_bound a c); order.
Qed.

(** In this convention, [div] performs Rounding-Toward-Bottom.

    Since we cannot speak of rational values here, we express this
    fact by multiplying back by [b], and this leads to separates
    statements according to the sign of [b].

    First, [a/b] is below the exact fraction ...
*)

Lemma mul_div_le : forall a b, 0<b -> b*(a/b) <= a.
Proof.
intros.
rewrite (div_mod a b) at 2; try order.
rewrite <- (add_0_r (b*(a/b))) at 1.
rewrite <- add_le_mono_l.
now destruct (mod_pos_bound a b).
Qed.

Lemma mul_div_ge : forall a b, b<0 -> a <= b*(a/b).
Proof.
intros. rewrite <- div_opp_opp, opp_le_mono, <-mul_opp_l by order.
apply mul_div_le. now rewrite opp_pos_neg.
Qed.

(** ... and moreover it is the larger such integer, since [S(a/b)]
    is strictly above the exact fraction.
*)

Lemma mul_succ_div_gt: forall a b, 0<b -> a < b*(S (a/b)).
Proof.
intros.
nzsimpl.
rewrite (div_mod a b) at 1; try order.
rewrite <- add_lt_mono_l.
destruct (mod_pos_bound a b); order.
Qed.

Lemma mul_succ_div_lt: forall a b, b<0 -> b*(S (a/b)) < a.
Proof.
intros. rewrite <- div_opp_opp, opp_lt_mono, <-mul_opp_l by order.
apply mul_succ_div_gt. now rewrite opp_pos_neg.
Qed.

(** NB: The four previous properties could be used as
    specifications for [div]. *)

(** Inequality [mul_div_le] is exact iff the modulo is zero. *)

Lemma div_exact : forall a b, b~=0 -> (a == b*(a/b) <-> a mod b == 0).
Proof.
intros.
rewrite (div_mod a b) at 1; try order.
rewrite <- (add_0_r (b*(a/b))) at 2.
apply add_cancel_l.
Qed.

(** Some additional inequalities about div. *)

Theorem div_lt_upper_bound:
  forall a b q, 0<b -> a < b*q -> a/b < q.
Proof.
intros.
rewrite (mul_lt_mono_pos_l b) by trivial.
apply le_lt_trans with a; trivial.
now apply mul_div_le.
Qed.

Theorem div_le_upper_bound:
  forall a b q, 0<b -> a <= b*q -> a/b <= q.
Proof.
intros.
rewrite <- (div_mul q b) by order.
apply div_le_mono; trivial. now rewrite mul_comm.
Qed.

Theorem div_le_lower_bound:
  forall a b q, 0<b -> b*q <= a -> q <= a/b.
Proof.
intros.
rewrite <- (div_mul q b) by order.
apply div_le_mono; trivial. now rewrite mul_comm.
Qed.

(** A division respects opposite monotonicity for the divisor *)

Lemma div_le_compat_l: forall p q r, 0<=p -> 0<q<=r -> p/r <= p/q.
Proof. exact div_le_compat_l. Qed.

(** * Relations between usual operations and mod and div *)

Lemma mod_add : forall a b c, c~=0 ->
 (a + b * c) mod c == a mod c.
Proof.
intros.
symmetry.
apply mod_unique with (a/c+b); trivial.
now apply mod_bound_or.
rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
now rewrite mul_comm.
Qed.

Lemma div_add : forall a b c, c~=0 ->
 (a + b * c) / c == a / c + b.
Proof.
intros.
apply (mul_cancel_l _ _ c); try order.
apply (add_cancel_r _ _ ((a+b*c) mod c)).
rewrite <- div_mod, mod_add by order.
rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
now rewrite mul_comm.
Qed.

Lemma div_add_l: forall a b c, b~=0 ->
 (a * b + c) / b == a + c / b.
Proof.
 intros a b c. rewrite (add_comm _ c), (add_comm a).
 now apply div_add.
Qed.

(** Cancellations. *)

Lemma div_mul_cancel_r : forall a b c, b~=0 -> c~=0 ->
 (a*c)/(b*c) == a/b.
Proof.
intros.
symmetry.
apply div_unique with ((a mod b)*c).
(* ineqs *)
destruct (lt_ge_cases 0 c).
rewrite <-(mul_0_l c), <-2mul_lt_mono_pos_r, <-2mul_le_mono_pos_r by trivial.
now apply mod_bound_or.
rewrite <-(mul_0_l c), <-2mul_lt_mono_neg_r, <-2mul_le_mono_neg_r by order.
destruct (mod_bound_or a b); tauto.
(* equation *)
rewrite (div_mod a b) at 1 by order.
rewrite mul_add_distr_r.
rewrite add_cancel_r.
rewrite <- 2 mul_assoc. now rewrite (mul_comm c).
Qed.

Lemma div_mul_cancel_l : forall a b c, b~=0 -> c~=0 ->
 (c*a)/(c*b) == a/b.
Proof.
intros. rewrite !(mul_comm c); now apply div_mul_cancel_r.
Qed.

Lemma mul_mod_distr_l: forall a b c, b~=0 -> c~=0 ->
  (c*a) mod (c*b) == c * (a mod b).
Proof.
intros.
rewrite <- (add_cancel_l _ _ ((c*b)* ((c*a)/(c*b)))).
rewrite <- div_mod.
rewrite div_mul_cancel_l by trivial.
rewrite <- mul_assoc, <- mul_add_distr_l, mul_cancel_l by order.
apply div_mod; order.
rewrite <- neq_mul_0; auto.
Qed.

Lemma mul_mod_distr_r: forall a b c, b~=0 -> c~=0 ->
  (a*c) mod (b*c) == (a mod b) * c.
Proof.
 intros. rewrite !(mul_comm _ c); now rewrite mul_mod_distr_l.
Qed.


(** Operations modulo. *)

Theorem mod_mod: forall a n, n~=0 ->
 (a mod n) mod n == a mod n.
Proof.
intros. rewrite mod_small_iff by trivial.
now apply mod_bound_or.
Qed.

Lemma mul_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)*b) mod n == (a*b) mod n.
Proof.
 intros a b n Hn. symmetry.
 rewrite (div_mod a n) at 1 by order.
 rewrite add_comm, (mul_comm n), (mul_comm _ b).
 rewrite mul_add_distr_l, mul_assoc.
 intros. rewrite mod_add by trivial.
 now rewrite mul_comm.
Qed.

Lemma mul_mod_idemp_r : forall a b n, n~=0 ->
 (a*(b mod n)) mod n == (a*b) mod n.
Proof.
 intros. rewrite !(mul_comm a). now apply mul_mod_idemp_l.
Qed.

Theorem mul_mod: forall a b n, n~=0 ->
 (a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof.
 intros. now rewrite mul_mod_idemp_l, mul_mod_idemp_r.
Qed.

Lemma add_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)+b) mod n == (a+b) mod n.
Proof.
 intros a b n Hn. symmetry.
 rewrite (div_mod a n) at 1 by order.
 rewrite <- add_assoc, add_comm, mul_comm.
 intros. now rewrite mod_add.
Qed.

Lemma add_mod_idemp_r : forall a b n, n~=0 ->
 (a+(b mod n)) mod n == (a+b) mod n.
Proof.
 intros. rewrite !(add_comm a). now apply add_mod_idemp_l.
Qed.

Theorem add_mod: forall a b n, n~=0 ->
 (a+b) mod n == (a mod n + b mod n) mod n.
Proof.
 intros. now rewrite add_mod_idemp_l, add_mod_idemp_r.
Qed.

(** With the current convention, the following result isn't always
    true with a negative last divisor. For instance
    [ 3/(-2)/(-2) = 1 <> 0 = 3 / (-2*-2) ], or
    [ 5/2/(-2) = -1 <> -2 = 5 / (2*-2) ]. *)

Lemma div_div : forall a b c, b~=0 -> 0<c ->
 (a/b)/c == a/(b*c).
Proof.
 intros a b c Hb Hc.
 apply div_unique with (b*((a/b) mod c) + a mod b).
 (* begin 0<= ... <b*c \/ ... *)
 apply neg_pos_cases in Hb. destruct Hb as [Hb|Hb].
 right.
 destruct (mod_pos_bound (a/b) c), (mod_neg_bound a b); trivial.
 split.
 apply le_lt_trans with (b*((a/b) mod c) + b).
 now rewrite <- mul_succ_r, <- mul_le_mono_neg_l, le_succ_l.
 now rewrite <- add_lt_mono_l.
 apply add_nonpos_nonpos; trivial.
 apply mul_nonpos_nonneg; order.
 left.
 destruct (mod_pos_bound (a/b) c), (mod_pos_bound a b); trivial.
 split.
 apply add_nonneg_nonneg; trivial.
 apply mul_nonneg_nonneg; order.
 apply lt_le_trans with (b*((a/b) mod c) + b).
 now rewrite <- add_lt_mono_l.
 now rewrite <- mul_succ_r, <- mul_le_mono_pos_l, le_succ_l.
 (* end 0<= ... < b*c \/ ... *)
 rewrite (div_mod a b) at 1 by order.
 rewrite add_assoc, add_cancel_r.
 rewrite <- mul_assoc, <- mul_add_distr_l, mul_cancel_l by order.
 apply div_mod; order.
Qed.

(** Similarly, the following result doesn't always hold when [c<0].
    For instance [3 mod (-2*-2)) = 3] while
    [3 mod (-2) + (-2)*((3/-2) mod -2) = -1].
*)

Lemma rem_mul_r : forall a b c, b~=0 -> 0<c ->
 a mod (b*c) == a mod b + b*((a/b) mod c).
Proof.
 intros a b c Hb Hc.
 apply add_cancel_l with (b*c*(a/(b*c))).
 rewrite <- div_mod by (apply neq_mul_0; split; order).
 rewrite <- div_div by trivial.
 rewrite add_assoc, add_shuffle0, <- mul_assoc, <- mul_add_distr_l.
 rewrite <- div_mod by order.
 apply div_mod; order.
Qed.

Lemma mod_div: forall a b, b~=0 ->
 a mod b / b == 0.
Proof.
 intros a b Hb.
 rewrite div_small_iff by assumption.
 auto using mod_bound_or.
Qed.

(** A last inequality: *)

Theorem div_mul_le:
 forall a b c, 0<=a -> 0<b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof. exact div_mul_le. Qed.

End ZDivProp.
