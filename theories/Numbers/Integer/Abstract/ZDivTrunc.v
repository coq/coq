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

(** * Euclidean Division for integers (Trunc convention)

    We use here the convention known as Trunc, or Round-Toward-Zero,
    where [a/b] is the integer with the largest absolute value to
    be between zero and the exact fraction. It can be summarized by:

    [a = bq+r /\ 0 <= |r| < |b| /\ Sign(r) = Sign(a)]

    This is the convention of Ocaml and many other systems (C, ASM, ...).
    This convention is named "T" in the following paper:

    R. Boute, "The Euclidean definition of the functions div and mod",
    ACM Transactions on Programming Languages and Systems,
    Vol. 14, No.2, pp. 127-144, April 1992.

    See files [ZDivFloor] and [ZDivEucl] for others conventions.
*)

Module Type ZQuotProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZSgnAbsProp A B).

(** We benefit from what already exists for NZ *)

 Module Import Private_Div.
 Module Quot2Div <: NZDiv A.
  Definition div := quot.
  Definition modulo := A.rem.
  Definition div_wd := quot_wd.
  Definition mod_wd := rem_wd.
  Definition div_mod := quot_rem.
  Definition mod_bound_pos := rem_bound_pos.
 End Quot2Div.
 Module NZQuot := Nop <+ NZDivProp A Quot2Div B.
 End Private_Div.

Ltac pos_or_neg a :=
 let LT := fresh "LT" in
 let LE := fresh "LE" in
 destruct (le_gt_cases 0 a) as [LE|LT]; [|rewrite <- opp_pos_neg in LT].

(** Another formulation of the main equation *)

Lemma rem_eq :
 forall a b, b~=0 -> a rem b == a - b*(a÷b).
Proof.
intros.
rewrite <- add_move_l.
symmetry. now apply quot_rem.
Qed.

(** A few sign rules (simple ones) *)

Lemma rem_opp_opp : forall a b, b ~= 0 -> (-a) rem (-b) == - (a rem b).
Proof. intros. now rewrite rem_opp_r, rem_opp_l. Qed.

Lemma quot_opp_l : forall a b, b ~= 0 -> (-a)÷b == -(a÷b).
Proof.
intros.
rewrite <- (mul_cancel_l _ _ b) by trivial.
rewrite <- (add_cancel_r _ _ ((-a) rem b)).
now rewrite <- quot_rem, rem_opp_l, mul_opp_r, <- opp_add_distr, <- quot_rem.
Qed.

Lemma quot_opp_r : forall a b, b ~= 0 -> a÷(-b) == -(a÷b).
Proof.
intros.
assert (-b ~= 0) by (now rewrite eq_opp_l, opp_0).
rewrite <- (mul_cancel_l _ _ (-b)) by trivial.
rewrite <- (add_cancel_r _ _ (a rem (-b))).
now rewrite <- quot_rem, rem_opp_r, mul_opp_opp, <- quot_rem.
Qed.

Lemma quot_opp_opp : forall a b, b ~= 0 -> (-a)÷(-b) == a÷b.
Proof. intros. now rewrite quot_opp_r, quot_opp_l, opp_involutive. Qed.

(** Uniqueness theorems *)

Theorem quot_rem_unique : forall b q1 q2 r1 r2 : t,
  (0<=r1<b \/ b<r1<=0) -> (0<=r2<b \/ b<r2<=0) ->
  b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof.
intros b q1 q2 r1 r2 Hr1 Hr2 EQ.
destruct Hr1; destruct Hr2; try (intuition; order).
apply NZQuot.div_mod_unique with b; trivial.
rewrite <- (opp_inj_wd r1 r2).
apply NZQuot.div_mod_unique with (-b); trivial.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; tauto.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; tauto.
now rewrite 2 mul_opp_l, <- 2 opp_add_distr, opp_inj_wd.
Qed.

Theorem quot_unique:
 forall a b q r, 0<=a -> 0<=r<b -> a == b*q + r -> q == a÷b.
Proof. intros; now apply NZQuot.div_unique with r. Qed.

Theorem rem_unique:
 forall a b q r, 0<=a -> 0<=r<b -> a == b*q + r -> r == a rem b.
Proof. intros; now apply NZQuot.mod_unique with q. Qed.

(** A division by itself returns 1 *)

Lemma quot_same : forall a, a~=0 -> a÷a == 1.
Proof.
intros. pos_or_neg a. apply NZQuot.div_same; order.
rewrite <- quot_opp_opp by trivial. now apply NZQuot.div_same.
Qed.

Lemma rem_same : forall a, a~=0 -> a rem a == 0.
Proof.
intros. rewrite rem_eq, quot_same by trivial. nzsimpl. apply sub_diag.
Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem quot_small: forall a b, 0<=a<b -> a÷b == 0.
Proof. exact NZQuot.div_small. Qed.

(** Same situation, in term of remulo: *)

Theorem rem_small: forall a b, 0<=a<b -> a rem b == a.
Proof. exact NZQuot.mod_small. Qed.

(** * Basic values of divisions and modulo. *)

Lemma quot_0_l: forall a, a~=0 -> 0÷a == 0.
Proof.
intros. pos_or_neg a. apply NZQuot.div_0_l; order.
rewrite <- quot_opp_opp, opp_0 by trivial. now apply NZQuot.div_0_l.
Qed.

Lemma rem_0_l: forall a, a~=0 -> 0 rem a == 0.
Proof.
intros; rewrite rem_eq, quot_0_l; now nzsimpl.
Qed.

Lemma quot_1_r: forall a, a÷1 == a.
Proof.
intros. pos_or_neg a. now apply NZQuot.div_1_r.
apply opp_inj. rewrite <- quot_opp_l. apply NZQuot.div_1_r; order.
intro EQ; symmetry in EQ; revert EQ; apply lt_neq, lt_0_1.
Qed.

Lemma rem_1_r: forall a, a rem 1 == 0.
Proof.
intros. rewrite rem_eq, quot_1_r; nzsimpl; auto using sub_diag.
intro EQ; symmetry in EQ; revert EQ; apply lt_neq; apply lt_0_1.
Qed.

Lemma quot_1_l: forall a, 1<a -> 1÷a == 0.
Proof. exact NZQuot.div_1_l. Qed.

Lemma rem_1_l: forall a, 1<a -> 1 rem a == 1.
Proof. exact NZQuot.mod_1_l. Qed.

Lemma quot_mul : forall a b, b~=0 -> (a*b)÷b == a.
Proof.
intros. pos_or_neg a; pos_or_neg b. apply NZQuot.div_mul; order.
rewrite <- quot_opp_opp, <- mul_opp_r by order. apply NZQuot.div_mul; order.
rewrite <- opp_inj_wd, <- quot_opp_l, <- mul_opp_l by order.
apply NZQuot.div_mul; order.
rewrite <- opp_inj_wd, <- quot_opp_r, <- mul_opp_opp by order.
apply NZQuot.div_mul; order.
Qed.

Lemma rem_mul : forall a b, b~=0 -> (a*b) rem b == 0.
Proof.
intros. rewrite rem_eq, quot_mul by trivial. rewrite mul_comm; apply sub_diag.
Qed.

Theorem quot_unique_exact a b q: b~=0 -> a == b*q -> q == a÷b.
Proof.
 intros Hb H. rewrite H, mul_comm. symmetry. now apply quot_mul.
Qed.

(** The sign of [a rem b] is the one of [a] (when it's not null) *)

Lemma rem_nonneg : forall a b, b~=0 -> 0 <= a -> 0 <= a rem b.
Proof.
 intros. pos_or_neg b. destruct (rem_bound_pos a b); order.
 rewrite <- rem_opp_r; trivial.
 destruct (rem_bound_pos a (-b)); trivial.
Qed.

Lemma rem_nonpos : forall a b, b~=0 -> a <= 0 -> a rem b <= 0.
Proof.
 intros a b Hb Ha.
 apply opp_nonneg_nonpos. apply opp_nonneg_nonpos in Ha.
 rewrite <- rem_opp_l by trivial. now apply rem_nonneg.
Qed.

Lemma rem_sign_mul : forall a b, b~=0 -> 0 <= (a rem b) * a.
Proof.
intros a b Hb. destruct (le_ge_cases 0 a).
 apply mul_nonneg_nonneg; trivial. now apply rem_nonneg.
 apply mul_nonpos_nonpos; trivial. now apply rem_nonpos.
Qed.

Lemma rem_sign_nz : forall a b, b~=0 -> a rem b ~= 0 ->
 sgn (a rem b) == sgn a.
Proof.
intros a b Hb H. destruct (lt_trichotomy 0 a) as [LT|[EQ|LT]].
rewrite 2 sgn_pos; try easy.
 generalize (rem_nonneg a b Hb (lt_le_incl _ _ LT)). order.
now rewrite <- EQ, rem_0_l, sgn_0.
rewrite 2 sgn_neg; try easy.
 generalize (rem_nonpos a b Hb (lt_le_incl _ _ LT)). order.
Qed.

Lemma rem_sign : forall a b, a~=0 -> b~=0 -> sgn (a rem b) ~= -sgn a.
Proof.
intros a b Ha Hb H.
destruct (eq_decidable (a rem b) 0) as [EQ|NEQ].
apply Ha, sgn_null_iff, opp_inj. now rewrite <- H, opp_0, EQ, sgn_0.
apply Ha, sgn_null_iff. apply eq_mul_0_l with 2; try order'. nzsimpl'.
apply add_move_0_l. rewrite <- H. symmetry. now apply rem_sign_nz.
Qed.

(** Operations and absolute value *)

Lemma rem_abs_l : forall a b, b ~= 0 -> (abs a) rem b == abs (a rem b).
Proof.
intros a b Hb. destruct (le_ge_cases 0 a) as [LE|LE].
rewrite 2 abs_eq; try easy. now apply rem_nonneg.
rewrite 2 abs_neq, rem_opp_l; try easy. now apply rem_nonpos.
Qed.

Lemma rem_abs_r : forall a b, b ~= 0 -> a rem (abs b) == a rem b.
Proof.
intros a b Hb. destruct (le_ge_cases 0 b).
now rewrite abs_eq. now rewrite abs_neq, ?rem_opp_r.
Qed.

Lemma rem_abs : forall a b,  b ~= 0 -> (abs a) rem (abs b) == abs (a rem b).
Proof.
intros. now rewrite rem_abs_r, rem_abs_l.
Qed.

Lemma quot_abs_l : forall a b, b ~= 0 -> (abs a)÷b == (sgn a)*(a÷b).
Proof.
intros a b Hb. destruct (lt_trichotomy 0 a) as [LT|[EQ|LT]].
rewrite abs_eq, sgn_pos by order. now nzsimpl.
rewrite <- EQ, abs_0, quot_0_l; trivial. now nzsimpl.
rewrite abs_neq, quot_opp_l, sgn_neg by order.
 rewrite mul_opp_l. now nzsimpl.
Qed.

Lemma quot_abs_r : forall a b, b ~= 0 -> a÷(abs b) == (sgn b)*(a÷b).
Proof.
intros a b Hb. destruct (lt_trichotomy 0 b) as [LT|[EQ|LT]].
rewrite abs_eq, sgn_pos by order. now nzsimpl.
order.
rewrite abs_neq, quot_opp_r, sgn_neg by order.
 rewrite mul_opp_l. now nzsimpl.
Qed.

Lemma quot_abs : forall a b, b ~= 0 -> (abs a)÷(abs b) == abs (a÷b).
Proof.
intros a b Hb.
pos_or_neg a; [rewrite (abs_eq a)|rewrite (abs_neq a)];
 try apply opp_nonneg_nonpos; try order.
pos_or_neg b; [rewrite (abs_eq b)|rewrite (abs_neq b)];
 try apply opp_nonneg_nonpos; try order.
rewrite abs_eq; try easy. apply NZQuot.div_pos; order.
rewrite <- abs_opp, <- quot_opp_r, abs_eq; try easy.
 apply NZQuot.div_pos; order.
pos_or_neg b; [rewrite (abs_eq b)|rewrite (abs_neq b)];
 try apply opp_nonneg_nonpos; try order.
rewrite <- (abs_opp (_÷_)), <- quot_opp_l, abs_eq; try easy.
 apply NZQuot.div_pos; order.
rewrite <- (quot_opp_opp a b), abs_eq; try easy.
 apply NZQuot.div_pos; order.
Qed.

(** We have a general bound for absolute values *)

Lemma rem_bound_abs :
 forall a b, b~=0 -> abs (a rem b) < abs b.
Proof.
intros. rewrite <- rem_abs; trivial.
apply rem_bound_pos. apply abs_nonneg. now apply abs_pos.
Qed.

(** * Order results about rem and quot *)

(** A modulo cannot grow beyond its starting point. *)

Theorem rem_le: forall a b, 0<=a -> 0<b -> a rem b <= a.
Proof. exact NZQuot.mod_le. Qed.

Theorem quot_pos : forall a b, 0<=a -> 0<b -> 0<= a÷b.
Proof. exact NZQuot.div_pos. Qed.

Lemma quot_str_pos : forall a b, 0<b<=a -> 0 < a÷b.
Proof. exact NZQuot.div_str_pos. Qed.

Lemma quot_small_iff : forall a b, b~=0 -> (a÷b==0 <-> abs a < abs b).
Proof.
intros. pos_or_neg a; pos_or_neg b.
rewrite NZQuot.div_small_iff; try order. rewrite 2 abs_eq; intuition; order.
rewrite <- opp_inj_wd, opp_0, <- quot_opp_r, NZQuot.div_small_iff by order.
 rewrite (abs_eq a), (abs_neq' b); intuition; order.
rewrite <- opp_inj_wd, opp_0, <- quot_opp_l, NZQuot.div_small_iff by order.
 rewrite (abs_neq' a), (abs_eq b); intuition; order.
rewrite <- quot_opp_opp, NZQuot.div_small_iff by order.
 rewrite (abs_neq' a), (abs_neq' b); intuition; order.
Qed.

Lemma rem_small_iff : forall a b, b~=0 -> (a rem b == a <-> abs a < abs b).
Proof.
intros. rewrite rem_eq, <- quot_small_iff by order.
rewrite sub_move_r, <- (add_0_r a) at 1. rewrite add_cancel_l.
rewrite eq_sym_iff, eq_mul_0. tauto.
Qed.

(** As soon as the divisor is strictly greater than 1,
    the division is strictly decreasing. *)

Lemma quot_lt : forall a b, 0<a -> 1<b -> a÷b < a.
Proof. exact NZQuot.div_lt. Qed.

(** [le] is compatible with a positive division. *)

Lemma quot_le_mono : forall a b c, 0<c -> a<=b -> a÷c <= b÷c.
Proof.
intros. pos_or_neg a. apply NZQuot.div_le_mono; auto.
pos_or_neg b. apply le_trans with 0.
 rewrite <- opp_nonneg_nonpos, <- quot_opp_l by order.
 apply quot_pos; order.
 apply quot_pos; order.
rewrite opp_le_mono in *. rewrite <- 2 quot_opp_l by order.
 apply NZQuot.div_le_mono; intuition; order.
Qed.

(** With this choice of division,
    rounding of quot is always done toward zero: *)

Lemma mul_quot_le : forall a b, 0<=a -> b~=0 -> 0 <= b*(a÷b) <= a.
Proof.
intros. pos_or_neg b.
split.
apply mul_nonneg_nonneg; [|apply quot_pos]; order.
apply NZQuot.mul_div_le; order.
rewrite <- mul_opp_opp, <- quot_opp_r by order.
split.
apply mul_nonneg_nonneg; [|apply quot_pos]; order.
apply NZQuot.mul_div_le; order.
Qed.

Lemma mul_quot_ge : forall a b, a<=0 -> b~=0 -> a <= b*(a÷b) <= 0.
Proof.
intros.
rewrite <- opp_nonneg_nonpos, opp_le_mono, <-mul_opp_r, <-quot_opp_l by order.
rewrite <- opp_nonneg_nonpos in *.
destruct (mul_quot_le (-a) b); tauto.
Qed.

(** For positive numbers, considering [S (a÷b)] leads to an upper bound for [a] *)

Lemma mul_succ_quot_gt: forall a b, 0<=a -> 0<b -> a < b*(S (a÷b)).
Proof. exact NZQuot.mul_succ_div_gt. Qed.

(** Similar results with negative numbers *)

Lemma mul_pred_quot_lt: forall a b, a<=0 -> 0<b -> b*(P (a÷b)) < a.
Proof.
intros.
rewrite opp_lt_mono, <- mul_opp_r, opp_pred, <- quot_opp_l by order.
rewrite <- opp_nonneg_nonpos in *.
now apply mul_succ_quot_gt.
Qed.

Lemma mul_pred_quot_gt: forall a b, 0<=a -> b<0 -> a < b*(P (a÷b)).
Proof.
intros.
rewrite <- mul_opp_opp, opp_pred, <- quot_opp_r by order.
rewrite <- opp_pos_neg in *.
now apply mul_succ_quot_gt.
Qed.

Lemma mul_succ_quot_lt: forall a b, a<=0 -> b<0 -> b*(S (a÷b)) < a.
Proof.
intros.
rewrite opp_lt_mono, <- mul_opp_l, <- quot_opp_opp by order.
rewrite <- opp_nonneg_nonpos, <- opp_pos_neg in *.
now apply mul_succ_quot_gt.
Qed.

(** Inequality [mul_quot_le] is exact iff the modulo is zero. *)

Lemma quot_exact : forall a b, b~=0 -> (a == b*(a÷b) <-> a rem b == 0).
Proof.
intros. rewrite rem_eq by order. rewrite sub_move_r; nzsimpl; tauto.
Qed.

(** Some additional inequalities about quot. *)

Theorem quot_lt_upper_bound:
  forall a b q, 0<=a -> 0<b -> a < b*q -> a÷b < q.
Proof. exact NZQuot.div_lt_upper_bound. Qed.

Theorem quot_le_upper_bound:
  forall a b q, 0<b -> a <= b*q -> a÷b <= q.
Proof.
intros.
rewrite <- (quot_mul q b) by order.
apply quot_le_mono; trivial. now rewrite mul_comm.
Qed.

Theorem quot_le_lower_bound:
  forall a b q, 0<b -> b*q <= a -> q <= a÷b.
Proof.
intros.
rewrite <- (quot_mul q b) by order.
apply quot_le_mono; trivial. now rewrite mul_comm.
Qed.

(** A division respects opposite monotonicity for the divisor *)

Lemma quot_le_compat_l: forall p q r, 0<=p -> 0<q<=r -> p÷r <= p÷q.
Proof. exact NZQuot.div_le_compat_l. Qed.

(** * Relations between usual operations and rem and quot *)

(** Unlike with other division conventions, some results here aren't
    always valid, and need to be restricted. For instance
    [(a+b*c) rem c <> a rem c] for [a=9,b=-5,c=2] *)

Lemma rem_add : forall a b c, c~=0 -> 0 <= (a+b*c)*a ->
 (a + b * c) rem c == a rem c.
Proof.
assert (forall a b c, c~=0 -> 0<=a -> 0<=a+b*c -> (a+b*c) rem c == a rem c).
 intros. pos_or_neg c. apply NZQuot.mod_add; order.
 rewrite <- (rem_opp_r a), <- (rem_opp_r (a+b*c)) by order.
 rewrite <- mul_opp_opp in *.
 apply NZQuot.mod_add; order.
intros a b c Hc Habc.
destruct (le_0_mul _ _ Habc) as [(Habc',Ha)|(Habc',Ha)]. auto.
apply opp_inj. revert Ha Habc'.
rewrite <- 2 opp_nonneg_nonpos.
rewrite <- 2 rem_opp_l, opp_add_distr, <- mul_opp_l by order. auto.
Qed.

Lemma quot_add : forall a b c, c~=0 -> 0 <= (a+b*c)*a ->
 (a + b * c) ÷ c == a ÷ c + b.
Proof.
intros.
rewrite <- (mul_cancel_l _ _ c) by trivial.
rewrite <- (add_cancel_r _ _ ((a+b*c) rem c)).
rewrite <- quot_rem, rem_add by trivial.
now rewrite mul_add_distr_l, add_shuffle0, <-quot_rem, mul_comm.
Qed.

Lemma quot_add_l: forall a b c, b~=0 -> 0 <= (a*b+c)*c ->
 (a * b + c) ÷ b == a + c ÷ b.
Proof.
 intros a b c. rewrite add_comm, (add_comm a). now apply quot_add.
Qed.

(** Cancellations. *)

Lemma quot_mul_cancel_r : forall a b c, b~=0 -> c~=0 ->
 (a*c)÷(b*c) == a÷b.
Proof.
assert (Aux1 : forall a b c, 0<=a -> 0<b -> c~=0 -> (a*c)÷(b*c) == a÷b).
 intros. pos_or_neg c. apply NZQuot.div_mul_cancel_r; order.
 rewrite <- quot_opp_opp, <- 2 mul_opp_r. apply NZQuot.div_mul_cancel_r; order.
 rewrite <- neq_mul_0; intuition order.
assert (Aux2 : forall a b c, 0<=a -> b~=0 -> c~=0 -> (a*c)÷(b*c) == a÷b).
 intros. pos_or_neg b. apply Aux1; order.
 apply opp_inj. rewrite <- 2 quot_opp_r, <- mul_opp_l; try order. apply Aux1; order.
 rewrite <- neq_mul_0; intuition order.
intros. pos_or_neg a. apply Aux2; order.
apply opp_inj. rewrite <- 2 quot_opp_l, <- mul_opp_l; try order. apply Aux2; order.
rewrite <- neq_mul_0; intuition order.
Qed.

Lemma quot_mul_cancel_l : forall a b c, b~=0 -> c~=0 ->
 (c*a)÷(c*b) == a÷b.
Proof.
intros. rewrite !(mul_comm c); now apply quot_mul_cancel_r.
Qed.

Lemma mul_rem_distr_r: forall a b c, b~=0 -> c~=0 ->
  (a*c) rem (b*c) == (a rem b) * c.
Proof.
intros.
assert (b*c ~= 0) by (rewrite <- neq_mul_0; tauto).
rewrite ! rem_eq by trivial.
rewrite quot_mul_cancel_r by order.
now rewrite mul_sub_distr_r, <- !mul_assoc, (mul_comm (a÷b) c).
Qed.

Lemma mul_rem_distr_l: forall a b c, b~=0 -> c~=0 ->
  (c*a) rem (c*b) == c * (a rem b).
Proof.
intros; rewrite !(mul_comm c); now apply mul_rem_distr_r.
Qed.

(** Operations modulo. *)

Theorem rem_rem: forall a n, n~=0 ->
 (a rem n) rem n == a rem n.
Proof.
intros. pos_or_neg a; pos_or_neg n. apply NZQuot.mod_mod; order.
rewrite <- ! (rem_opp_r _ n) by trivial. apply NZQuot.mod_mod; order.
apply opp_inj. rewrite <- !rem_opp_l by order. apply NZQuot.mod_mod; order.
apply opp_inj. rewrite <- !rem_opp_opp by order. apply NZQuot.mod_mod; order.
Qed.

Lemma mul_rem_idemp_l : forall a b n, n~=0 ->
 ((a rem n)*b) rem n == (a*b) rem n.
Proof.
assert (Aux1 : forall a b n, 0<=a -> 0<=b -> n~=0 ->
         ((a rem n)*b) rem n == (a*b) rem n).
 intros. pos_or_neg n. apply NZQuot.mul_mod_idemp_l; order.
 rewrite <- ! (rem_opp_r _ n) by order. apply NZQuot.mul_mod_idemp_l; order.
assert (Aux2 : forall a b n, 0<=a -> n~=0 ->
         ((a rem n)*b) rem n == (a*b) rem n).
 intros. pos_or_neg b. now apply Aux1.
 apply opp_inj. rewrite <-2 rem_opp_l, <-2 mul_opp_r by order.
  apply Aux1; order.
intros a b n Hn. pos_or_neg a. now apply Aux2.
apply opp_inj. rewrite <-2 rem_opp_l, <-2 mul_opp_l, <-rem_opp_l by order.
apply Aux2; order.
Qed.

Lemma mul_rem_idemp_r : forall a b n, n~=0 ->
 (a*(b rem n)) rem n == (a*b) rem n.
Proof.
intros. rewrite !(mul_comm a). now apply mul_rem_idemp_l.
Qed.

Theorem mul_rem: forall a b n, n~=0 ->
 (a * b) rem n == ((a rem n) * (b rem n)) rem n.
Proof.
intros. now rewrite mul_rem_idemp_l, mul_rem_idemp_r.
Qed.

(** addition and modulo

  Generally speaking, unlike with other conventions, we don't have
       [(a+b) rem n = (a rem n + b rem n) rem n]
  for any a and b.
  For instance, take (8 + (-10)) rem 3 = -2 whereas
  (8 rem 3 + (-10 rem 3)) rem 3 = 1.
*)

Lemma add_rem_idemp_l : forall a b n, n~=0 -> 0 <= a*b ->
 ((a rem n)+b) rem n == (a+b) rem n.
Proof.
assert (Aux : forall a b n, 0<=a -> 0<=b -> n~=0 ->
          ((a rem n)+b) rem n == (a+b) rem n).
 intros. pos_or_neg n. apply NZQuot.add_mod_idemp_l; order.
 rewrite <- ! (rem_opp_r _ n) by order. apply NZQuot.add_mod_idemp_l; order.
intros a b n Hn Hab. destruct (le_0_mul _ _ Hab) as [(Ha,Hb)|(Ha,Hb)].
now apply Aux.
apply opp_inj. rewrite <-2 rem_opp_l, 2 opp_add_distr, <-rem_opp_l by order.
rewrite <- opp_nonneg_nonpos in *.
now apply Aux.
Qed.

Lemma add_rem_idemp_r : forall a b n, n~=0 -> 0 <= a*b ->
 (a+(b rem n)) rem n == (a+b) rem n.
Proof.
intros. rewrite !(add_comm a). apply add_rem_idemp_l; trivial.
now rewrite mul_comm.
Qed.

Theorem add_rem: forall a b n, n~=0 -> 0 <= a*b ->
 (a+b) rem n == (a rem n + b rem n) rem n.
Proof.
intros a b n Hn Hab. rewrite add_rem_idemp_l, add_rem_idemp_r; trivial.
reflexivity.
destruct (le_0_mul _ _ Hab) as [(Ha,Hb)|(Ha,Hb)];
 destruct (le_0_mul _ _ (rem_sign_mul b n Hn)) as [(Hb',Hm)|(Hb',Hm)];
 auto using mul_nonneg_nonneg, mul_nonpos_nonpos.
 setoid_replace b with 0 by order. rewrite rem_0_l by order. nzsimpl; order.
 setoid_replace b with 0 by order. rewrite rem_0_l by order. nzsimpl; order.
Qed.

(** Conversely, the following results need less restrictions here. *)

Lemma quot_quot : forall a b c, b~=0 -> c~=0 ->
 (a÷b)÷c == a÷(b*c).
Proof.
assert (Aux1 : forall a b c, 0<=a -> 0<b -> c~=0 -> (a÷b)÷c == a÷(b*c)).
 intros. pos_or_neg c. apply NZQuot.div_div; order.
 apply opp_inj. rewrite <- 2 quot_opp_r, <- mul_opp_r; trivial.
 apply NZQuot.div_div; order.
 rewrite <- neq_mul_0; intuition order.
assert (Aux2 : forall a b c, 0<=a -> b~=0 -> c~=0 -> (a÷b)÷c == a÷(b*c)).
 intros. pos_or_neg b. apply Aux1; order.
 apply opp_inj. rewrite <- quot_opp_l, <- 2 quot_opp_r, <- mul_opp_l; trivial.
 apply Aux1; trivial.
 rewrite <- neq_mul_0; intuition order.
intros. pos_or_neg a. apply Aux2; order.
apply opp_inj. rewrite <- 3 quot_opp_l; try order. apply Aux2; order.
rewrite <- neq_mul_0. tauto.
Qed.

Lemma mod_mul_r : forall a b c, b~=0 -> c~=0 ->
 a rem (b*c) == a rem b + b*((a÷b) rem c).
Proof.
 intros a b c Hb Hc.
 apply add_cancel_l with (b*c*(a÷(b*c))).
 rewrite <- quot_rem by (apply neq_mul_0; split; order).
 rewrite <- quot_quot by trivial.
 rewrite add_assoc, add_shuffle0, <- mul_assoc, <- mul_add_distr_l.
 rewrite <- quot_rem by order.
 apply quot_rem; order.
Qed.

Lemma rem_quot: forall a b, b~=0 ->
 a rem b ÷ b == 0.
Proof.
 intros a b Hb.
 rewrite quot_small_iff by assumption.
 auto using rem_bound_abs.
Qed.

(** A last inequality: *)

Theorem quot_mul_le:
 forall a b c, 0<=a -> 0<b -> 0<=c -> c*(a÷b) <= (c*a)÷b.
Proof. exact NZQuot.div_mul_le. Qed.

End ZQuotProp.

