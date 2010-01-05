(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

Require Import ZAxioms ZProperties NZDiv.

Open Scope NumScope.

Module Type ZDiv (Import Z : ZAxiomsSig).
 Include Type NZDivCommon Z. (** div, mod, compat with eq, equation a=bq+r *)
 Axiom mod_bound : forall a b, 0<=a -> 0<b -> 0 <= a mod b < b.
 Axiom mod_opp_l : forall a b, b ~= 0 -> (-a) mod b == - (a mod b).
 Axiom mod_opp_r : forall a b, b ~= 0 -> a mod (-b) == a mod b.
End ZDiv.

Module Type ZDivSig := ZAxiomsSig <+ ZDiv.

Module ZDivPropFunct (Import Z : ZDivSig).
 (* TODO: en faire un arg du foncteur + comprendre le bug de SearchAbout *)
 Module Import ZP := ZPropFunct Z.

(** We benefit from what already exists for NZ *)

 Module Import NZDivP := NZDivPropFunct Z.

Ltac pos_or_neg a :=
 let LT := fresh "LT" in
 let LE := fresh "LE" in
 destruct (le_gt_cases 0 a) as [LE|LT]; [|rewrite <- opp_pos_neg in LT].

(** Another formulation of the main equation *)

Lemma mod_eq :
 forall a b, b~=0 -> a mod b == a - b*(a/b).
Proof.
intros.
rewrite <- add_move_l.
symmetry. apply div_mod; auto.
Qed.

(** A few sign rules (simple ones) *)

Lemma mod_opp_opp : forall a b, b ~= 0 -> (-a) mod (-b) == - (a mod b).
Proof. intros. rewrite mod_opp_r, mod_opp_l; auto. Qed.

Lemma div_opp_l : forall a b, b ~= 0 -> (-a)/b == -(a/b).
Proof.
intros.
rewrite <- (mul_cancel_l _ _ b); auto.
rewrite <- (add_cancel_r _ _ ((-a) mod b)); auto.
rewrite <- div_mod; auto.
rewrite mod_opp_l, mul_opp_r, <- opp_add_distr, <- div_mod; auto.
Qed.

Lemma div_opp_r : forall a b, b ~= 0 -> a/(-b) == -(a/b).
Proof.
intros.
assert (-b ~= 0) by (rewrite eq_opp_l, opp_0; auto).
rewrite <- (mul_cancel_l _ _ (-b)); auto.
rewrite <- (add_cancel_r _ _ (a mod (-b))); auto.
rewrite <- div_mod; auto.
rewrite mod_opp_r, mul_opp_opp, <- div_mod; auto.
Qed.

Lemma div_opp_opp : forall a b, b ~= 0 -> (-a)/(-b) == a/b.
Proof. intros. rewrite div_opp_r, div_opp_l, opp_involutive; auto. Qed.

(** The sign of [a mod b] is the one of [a] *)

(* TODO: a proper sgn function and theory *)

Lemma mod_sign : forall a b, b~=0 -> 0 <= (a mod b) * a.
Proof.
assert (Aux : forall a b, 0<b -> 0 <= (a mod b) * a).
 intros. pos_or_neg a.
 apply mul_nonneg_nonneg; auto. destruct (mod_bound a b); auto.
 rewrite <- mul_opp_opp, <- mod_opp_l by order.
 apply mul_nonneg_nonneg; try order. destruct (mod_bound (-a) b); try order.
intros. pos_or_neg b. apply Aux; order.
rewrite <- mod_opp_r by order. apply Aux; order.
Qed.


(** Uniqueness theorems *)

Theorem div_mod_unique : forall b q1 q2 r1 r2 : t,
  (0<=r1<b \/ b<r1<=0) -> (0<=r2<b \/ b<r2<=0) ->
  b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof.
intros b q1 q2 r1 r2 Hr1 Hr2 EQ.
destruct Hr1; destruct Hr2; try (intuition; order).
apply div_mod_unique with b; auto.
rewrite <- opp_inj_wd in EQ.
rewrite 2 opp_add_distr in EQ. rewrite <- 2 mul_opp_l in EQ.
rewrite <- (opp_inj_wd r1 r2).
apply div_mod_unique with (-b); auto.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; intuition.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; intuition.
Qed.

Theorem div_unique:
 forall a b q r, 0<=a -> 0<=r<b -> a == b*q + r -> q == a/b.
Proof. intros; apply div_unique with r; auto. Qed.

Theorem mod_unique:
 forall a b q r, 0<=a -> 0<=r<b -> a == b*q + r -> r == a mod b.
Proof. intros; apply mod_unique with q; auto. Qed.

(** A division by itself returns 1 *)

Lemma div_same : forall a, a~=0 -> a/a == 1.
Proof.
intros. pos_or_neg a. apply div_same; order.
rewrite <- div_opp_opp; auto. apply div_same; auto.
Qed.

Lemma mod_same : forall a, a~=0 -> a mod a == 0.
Proof.
intros. rewrite mod_eq, div_same; auto. nzsimpl. apply sub_diag.
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
rewrite <- div_opp_opp, opp_0; auto. apply div_0_l; auto.
Qed.

Lemma mod_0_l: forall a, a~=0 -> 0 mod a == 0.
Proof.
intros; rewrite mod_eq, div_0_l; nzsimpl; auto.
Qed.

Lemma div_1_r: forall a, a/1 == a.
Proof.
intros. pos_or_neg a. apply div_1_r; auto.
apply opp_inj. rewrite <- div_opp_l. apply div_1_r; order.
intro EQ; symmetry in EQ; revert EQ; apply lt_neq, lt_0_1.
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
intros. pos_or_neg a; pos_or_neg b. apply div_mul; order.
rewrite <- div_opp_opp, <- mul_opp_r by order. apply div_mul; order.
rewrite <- opp_inj_wd, <- div_opp_l, <- mul_opp_l by order. apply div_mul; order.
rewrite <- opp_inj_wd, <- div_opp_r, <- mul_opp_opp by order. apply div_mul; order.
Qed.

Lemma mod_mul : forall a b, b~=0 -> (a*b) mod b == 0.
Proof.
intros. rewrite mod_eq, div_mul; auto. rewrite mul_comm; apply sub_diag.
Qed.

(** * Order results about mod and div *)

(** A modulo cannot grow beyond its starting point. *)

Theorem mod_le: forall a b, 0<=a -> 0<b -> a mod b <= a.
Proof. exact mod_le. Qed.

Theorem div_pos : forall a b, 0<=a -> 0<b -> 0<= a/b.
Proof. exact div_pos. Qed.

Lemma div_str_pos : forall a b, 0<b<=a -> 0 < a/b.
Proof. exact div_str_pos. Qed.

(** TODO: TO MIGRATE LATER *)
Definition abs z := max z (-z).
Lemma abs_pos : forall z, 0<=z -> abs z == z.
Proof.
intros; apply max_l. apply le_trans with 0; auto.
rewrite opp_nonpos_nonneg; auto.
Qed.
Lemma abs_neg : forall z, 0<=-z -> abs z == -z.
Proof.
intros; apply max_r. apply le_trans with 0; auto.
rewrite <- opp_nonneg_nonpos; auto.
Qed.

(** END TODO *)

Lemma div_small_iff : forall a b, b~=0 -> (a/b==0 <-> abs a < abs b).
Proof.
intros. pos_or_neg a; pos_or_neg b.
rewrite div_small_iff; try order. rewrite 2 abs_pos; intuition; order.
rewrite <- opp_inj_wd, opp_0, <- div_opp_r, div_small_iff by order.
 rewrite (abs_pos a), (abs_neg b); intuition; order.
rewrite <- opp_inj_wd, opp_0, <- div_opp_l, div_small_iff by order.
 rewrite (abs_neg a), (abs_pos b); intuition; order.
rewrite <- div_opp_opp, div_small_iff by order.
 rewrite (abs_neg a), (abs_neg b); intuition; order.
Qed.

Lemma mod_small_iff : forall a b, b~=0 -> (a mod b == a <-> abs a < abs b).
Proof.
intros. rewrite mod_eq, <- div_small_iff by order.
rewrite sub_move_r, <- (add_0_r a) at 1. rewrite add_cancel_l.
rewrite eq_sym_iff, eq_mul_0. intuition.
Qed.

(** As soon as the divisor is strictly greater than 1,
    the division is strictly decreasing. *)

Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof. exact div_lt. Qed.

(** [le] is compatible with a positive division. *)

Lemma div_le_mono : forall a b c, 0<c -> a<=b -> a/c <= b/c.
Proof.
intros. pos_or_neg a. apply div_le_mono; auto.
pos_or_neg b. apply le_trans with 0.
 rewrite <- opp_nonneg_nonpos, <- div_opp_l by order.
 apply div_pos; order.
 apply div_pos; order.
rewrite opp_le_mono in *. rewrite <- 2 div_opp_l by order.
 apply div_le_mono; intuition; order.
Qed.

(** With this choice of division,
    rounding of div is always done toward zero: *)

Lemma mul_div_le : forall a b, 0<=a -> b~=0 -> 0 <= b*(a/b) <= a.
Proof.
intros. pos_or_neg b.
split.
apply mul_nonneg_nonneg; [|apply div_pos]; order.
apply mul_div_le; order.
rewrite <- mul_opp_opp, <- div_opp_r by order.
split.
apply mul_nonneg_nonneg; [|apply div_pos]; order.
apply mul_div_le; order.
Qed.

Lemma mul_div_ge : forall a b, a<=0 -> b~=0 -> a <= b*(a/b) <= 0.
Proof.
intros.
rewrite <- opp_nonneg_nonpos, opp_le_mono, <-mul_opp_r, <-div_opp_l by order.
destruct (mul_div_le (-a) b); auto.
rewrite opp_nonneg_nonpos; auto.
Qed.

(** For positive numbers, considering [S (a/b)] leads to an upper bound for [a] *)

Lemma mul_succ_div_gt: forall a b, 0<=a -> 0<b -> a < b*(S (a/b)).
Proof. exact mul_succ_div_gt. Qed.

(** Similar results with negative numbers *)

Lemma mul_pred_div_lt: forall a b, a<=0 -> 0<b -> b*(P (a/b)) < a.
Proof.
intros.
rewrite opp_lt_mono, <- mul_opp_r, opp_pred, <- div_opp_l by order.
apply mul_succ_div_gt; auto.
rewrite opp_nonneg_nonpos; auto.
Qed.

Lemma mul_pred_div_gt: forall a b, 0<=a -> b<0 -> a < b*(P (a/b)).
Proof.
intros.
rewrite <- mul_opp_opp, opp_pred, <- div_opp_r by order.
apply mul_succ_div_gt; auto.
rewrite opp_pos_neg; auto.
Qed.

Lemma mul_succ_div_lt: forall a b, a<=0 -> b<0 -> b*(S (a/b)) < a.
Proof.
intros.
rewrite opp_lt_mono, <- mul_opp_l, <- div_opp_opp by order.
apply mul_succ_div_gt; auto.
rewrite opp_nonneg_nonpos; auto.
rewrite opp_pos_neg; auto.
Qed.

(** Inequality [mul_div_le] is exact iff the modulo is zero. *)

Lemma div_exact : forall a b, b~=0 -> (a == b*(a/b) <-> a mod b == 0).
Proof.
intros. rewrite mod_eq by order. rewrite sub_move_r; nzsimpl; intuition.
Qed.

(** Some additionnal inequalities about div. *)

Theorem div_lt_upper_bound:
  forall a b q, 0<=a -> 0<b -> a < b*q -> a/b < q.
Proof. exact div_lt_upper_bound. Qed.

Theorem div_le_upper_bound:
  forall a b q, 0<b -> a <= b*q -> a/b <= q.
Proof.
intros.
rewrite <- (div_mul q b) by order.
apply div_le_mono; auto. rewrite mul_comm; auto.
Qed.

Theorem div_le_lower_bound:
  forall a b q, 0<b -> b*q <= a -> q <= a/b.
Proof.
intros.
rewrite <- (div_mul q b) by order.
apply div_le_mono; auto. rewrite mul_comm; auto.
Qed.

(** A division respects opposite monotonicity for the divisor *)

Lemma div_le_compat_l: forall p q r, 0<=p -> 0<q<=r -> p/r <= p/q.
Proof. exact div_le_compat_l. Qed.

(** * Relations between usual operations and mod and div *)

(** Unlike with other division conventions, some results here aren't
    always valid, and need to be restricted. For instance
    [(a+b*c) mod c <> a mod c] for [a=9,b=-5,c=2] *)

Lemma mod_add : forall a b c, c~=0 -> 0 <= (a+b*c)*a ->
 (a + b * c) mod c == a mod c.
Proof.
assert (forall a b c, c~=0 -> 0<=a -> 0<=a+b*c -> (a+b*c) mod c == a mod c).
 intros. pos_or_neg c. apply mod_add; order.
 rewrite <- (mod_opp_r a), <- (mod_opp_r (a+b*c)) by order.
 rewrite <- mul_opp_opp in *.
 apply mod_add; order.
intros a b c Hc Habc.
destruct (le_0_mul _ _ Habc) as [(Habc',Ha)|(Habc',Ha)]; auto.
apply opp_inj. revert Ha Habc'.
rewrite <- 2 opp_nonneg_nonpos.
rewrite <- 2 mod_opp_l, opp_add_distr, <- mul_opp_l by order; auto.
Qed.

Lemma div_add : forall a b c, c~=0 -> 0 <= (a+b*c)*a ->
 (a + b * c) / c == a / c + b.
Proof.
intros.
rewrite <- (mul_cancel_l _ _ c) by auto.
rewrite <- (add_cancel_r _ _ ((a+b*c) mod c)).
rewrite <- div_mod; auto.
rewrite mod_add; auto.
rewrite mul_add_distr_l, add_shuffle0, <-div_mod, mul_comm; auto.
Qed.

Lemma div_add_l: forall a b c, b~=0 -> 0 <= (a*b+c)*c ->
 (a * b + c) / b == a + c / b.
Proof.
 intros a b c. rewrite add_comm, (add_comm a). intros; apply div_add; auto.
Qed.

(** Cancellations. *)

Lemma div_mul_cancel_r : forall a b c, b~=0 -> c~=0 ->
 (a*c)/(b*c) == a/b.
Proof.
assert (Aux1 : forall a b c, 0<=a -> 0<b -> c~=0 -> (a*c)/(b*c) == a/b).
 intros. pos_or_neg c. apply div_mul_cancel_r; order.
 rewrite <- div_opp_opp, <- 2 mul_opp_r. apply div_mul_cancel_r; order.
 rewrite <- neq_mul_0; intuition order.
assert (Aux2 : forall a b c, 0<=a -> b~=0 -> c~=0 -> (a*c)/(b*c) == a/b).
 intros. pos_or_neg b. apply Aux1; order.
 apply opp_inj. rewrite <- 2 div_opp_r, <- mul_opp_l; try order. apply Aux1; order.
 rewrite <- neq_mul_0; intuition order.
intros. pos_or_neg a. apply Aux2; order.
apply opp_inj. rewrite <- 2 div_opp_l, <- mul_opp_l; try order. apply Aux2; order.
rewrite <- neq_mul_0; intuition order.
Qed.

Lemma div_mul_cancel_l : forall a b c, b~=0 -> c~=0 ->
 (c*a)/(c*b) == a/b.
Proof.
intros. rewrite !(mul_comm c); apply div_mul_cancel_r; auto.
Qed.

Lemma mul_mod_distr_r: forall a b c, b~=0 -> c~=0 ->
  (a*c) mod (b*c) == (a mod b) * c.
Proof.
intros.
assert (b*c ~= 0) by (rewrite <- neq_mul_0; intuition).
rewrite ! mod_eq by auto.
rewrite div_mul_cancel_r by order.
rewrite mul_sub_distr_r, <- !mul_assoc, (mul_comm (a/b) c); auto.
Qed.

Lemma mul_mod_distr_l: forall a b c, b~=0 -> c~=0 ->
  (c*a) mod (c*b) == c * (a mod b).
Proof.
intros; rewrite !(mul_comm c); apply mul_mod_distr_r; auto.
Qed.

(** Operations modulo. *)

Theorem mod_mod: forall a n, n~=0 ->
 (a mod n) mod n == a mod n.
Proof.
intros. pos_or_neg a; pos_or_neg n. apply mod_mod; order.
rewrite <- ! (mod_opp_r _ n) by auto. apply mod_mod; order.
apply opp_inj. rewrite <- !mod_opp_l by order. apply mod_mod; order.
apply opp_inj. rewrite <- !mod_opp_opp by order. apply mod_mod; order.
Qed.

Lemma mul_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)*b) mod n == (a*b) mod n.
Proof.
assert (Aux1 : forall a b n, 0<=a -> 0<=b -> n~=0 ->
         ((a mod n)*b) mod n == (a*b) mod n).
 intros. pos_or_neg n. apply mul_mod_idemp_l; order.
 rewrite <- ! (mod_opp_r _ n) by order. apply mul_mod_idemp_l; order.
assert (Aux2 : forall a b n, 0<=a -> n~=0 ->
         ((a mod n)*b) mod n == (a*b) mod n).
 intros. pos_or_neg b. apply Aux1; auto.
 apply opp_inj. rewrite <-2 mod_opp_l, <-2 mul_opp_r by order.
  apply Aux1; order.
intros a b n Hn. pos_or_neg a. apply Aux2; auto.
apply opp_inj. rewrite <-2 mod_opp_l, <-2 mul_opp_l, <-mod_opp_l by order.
apply Aux2; order.
Qed.

Lemma mul_mod_idemp_r : forall a b n, n~=0 ->
 (a*(b mod n)) mod n == (a*b) mod n.
Proof.
intros. rewrite !(mul_comm a). apply mul_mod_idemp_l; auto.
Qed.

Theorem mul_mod: forall a b n, n~=0 ->
 (a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof.
intros. rewrite mul_mod_idemp_l, mul_mod_idemp_r; auto.
Qed.

(** addition and modulo

  Generally speaking, unlike with other conventions, we don't have
       [(a+b) mod n = (a mod n + b mod n) mod n]
  for any a and b.
  For instance, take (8 + (-10)) mod 3 = -2 whereas
  (8 mod 3 + (-10 mod 3)) mod 3 = 1.
*)

Lemma add_mod_idemp_l : forall a b n, n~=0 -> 0 <= a*b ->
 ((a mod n)+b) mod n == (a+b) mod n.
Proof.
assert (Aux : forall a b n, 0<=a -> 0<=b -> n~=0 ->
          ((a mod n)+b) mod n == (a+b) mod n).
 intros. pos_or_neg n. apply add_mod_idemp_l; order.
 rewrite <- ! (mod_opp_r _ n) by order. apply add_mod_idemp_l; order.
intros a b n Hn Hab. destruct (le_0_mul _ _ Hab) as [(Ha,Hb)|(Ha,Hb)].
apply Aux; auto.
apply opp_inj. rewrite <-2 mod_opp_l, 2 opp_add_distr, <-mod_opp_l by order.
apply Aux; auto.
rewrite opp_nonneg_nonpos; auto.
rewrite opp_nonneg_nonpos; auto.
Qed.

Lemma add_mod_idemp_r : forall a b n, n~=0 -> 0 <= a*b ->
 (a+(b mod n)) mod n == (a+b) mod n.
Proof.
intros. rewrite !(add_comm a). apply add_mod_idemp_l; auto.
rewrite mul_comm; auto.
Qed.

Theorem add_mod: forall a b n, n~=0 -> 0 <= a*b ->
 (a+b) mod n == (a mod n + b mod n) mod n.
Proof.
intros a b n Hn Hab. rewrite add_mod_idemp_l, add_mod_idemp_r; auto.
destruct (le_0_mul _ _ Hab) as [(Ha,Hb)|(Ha,Hb)];
 destruct (le_0_mul _ _ (mod_sign b n Hn)) as [(Hb',Hm)|(Hb',Hm)];
 auto using mul_nonneg_nonneg, mul_nonpos_nonpos.
 setoid_replace b with 0 by order. rewrite mod_0_l by order. nzsimpl; order.
 setoid_replace b with 0 by order. rewrite mod_0_l by order. nzsimpl; order.
Qed.


(** Conversely, the following result needs less restrictions here. *)

Lemma div_div : forall a b c, b~=0 -> c~=0 ->
 (a/b)/c == a/(b*c).
Proof.
assert (Aux1 : forall a b c, 0<=a -> 0<b -> c~=0 -> (a/b)/c == a/(b*c)).
 intros. pos_or_neg c. apply div_div; order.
 apply opp_inj. rewrite <- 2 div_opp_r, <- mul_opp_r; auto. apply div_div; order.
 rewrite <- neq_mul_0; intuition order.
assert (Aux2 : forall a b c, 0<=a -> b~=0 -> c~=0 -> (a/b)/c == a/(b*c)).
 intros. pos_or_neg b. apply Aux1; order.
 apply opp_inj. rewrite <- div_opp_l, <- 2 div_opp_r, <- mul_opp_l; auto.
 rewrite <- neq_mul_0; intuition order.
intros. pos_or_neg a. apply Aux2; order.
apply opp_inj. rewrite <- 3 div_opp_l; try order. apply Aux2; order.
rewrite <- neq_mul_0; intuition order.
Qed.

(** A last inequality: *)

Theorem div_mul_le:
 forall a b c, 0<=a -> 0<b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof. exact div_mul_le. Qed.

(** mod is related to divisibility *)

Lemma mod_divides : forall a b, b~=0 ->
 (a mod b == 0 <-> exists c, a == b*c).
Proof.
 intros a b Hb. split.
 intros Hab. exists (a/b). rewrite (div_mod a b Hb) at 1.
  rewrite Hab; nzsimpl; auto.
 intros (c,Hc). rewrite Hc, mul_comm. apply mod_mul; auto.
Qed.

End ZDivPropFunct.

