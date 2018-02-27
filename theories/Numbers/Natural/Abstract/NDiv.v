(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import NAxioms NSub NZDiv.

(** Properties of Euclidean Division *)

Module Type NDivProp (Import N : NAxiomsSig')(Import NP : NSubProp N).

(** We benefit from what already exists for NZ *)
Module Import Private_NZDiv := Nop <+ NZDivProp N N NP.

Ltac auto' := try rewrite <- neq_0_lt_0; auto using le_0_l.

(** Let's now state again theorems, but without useless hypothesis. *)

Lemma mod_upper_bound : forall a b, b ~= 0 -> a mod b < b.
Proof. intros. apply mod_bound_pos; auto'. Qed.

(** Another formulation of the main equation *)

Lemma mod_eq :
 forall a b, b~=0 -> a mod b == a - b*(a/b).
Proof.
intros.
symmetry. apply add_sub_eq_l. symmetry.
now apply div_mod.
Qed.

(** Uniqueness theorems *)

Theorem div_mod_unique :
 forall b q1 q2 r1 r2, r1<b -> r2<b ->
  b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof. intros. apply div_mod_unique with b; auto'. Qed.

Theorem div_unique:
 forall a b q r, r<b -> a == b*q + r -> q == a/b.
Proof. intros; apply div_unique with r; auto'. Qed.

Theorem mod_unique:
 forall a b q r, r<b -> a == b*q + r -> r == a mod b.
Proof. intros. apply mod_unique with q; auto'. Qed.

Theorem div_unique_exact: forall a b q, b~=0 -> a == b*q -> q == a/b.
Proof. intros. apply div_unique_exact; auto'. Qed.

(** A division by itself returns 1 *)

Lemma div_same : forall a, a~=0 -> a/a == 1.
Proof. intros. apply div_same; auto'. Qed.

Lemma mod_same : forall a, a~=0 -> a mod a == 0.
Proof. intros. apply mod_same; auto'. Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem div_small: forall a b, a<b -> a/b == 0.
Proof. intros. apply div_small; auto'. Qed.

(** Same situation, in term of modulo: *)

Theorem mod_small: forall a b, a<b -> a mod b == a.
Proof. intros. apply mod_small; auto'. Qed.

(** * Basic values of divisions and modulo. *)

Lemma div_0_l: forall a, a~=0 -> 0/a == 0.
Proof. intros. apply div_0_l; auto'. Qed.

Lemma mod_0_l: forall a, a~=0 -> 0 mod a == 0.
Proof. intros. apply mod_0_l; auto'. Qed.

Lemma div_1_r: forall a, a/1 == a.
Proof. intros. apply div_1_r; auto'. Qed.

Lemma mod_1_r: forall a, a mod 1 == 0.
Proof. intros. apply mod_1_r; auto'. Qed.

Lemma div_1_l: forall a, 1<a -> 1/a == 0.
Proof. exact div_1_l. Qed.

Lemma mod_1_l: forall a, 1<a -> 1 mod a == 1.
Proof. exact mod_1_l. Qed.

Lemma div_mul : forall a b, b~=0 -> (a*b)/b == a.
Proof. intros. apply div_mul; auto'. Qed.

Lemma mod_mul : forall a b, b~=0 -> (a*b) mod b == 0.
Proof. intros. apply mod_mul; auto'. Qed.


(** * Order results about mod and div *)

(** A modulo cannot grow beyond its starting point. *)

Theorem mod_le: forall a b, b~=0 -> a mod b <= a.
Proof. intros. apply mod_le; auto'. Qed.

Lemma div_str_pos : forall a b, 0<b<=a -> 0 < a/b.
Proof. exact div_str_pos. Qed.

Lemma div_small_iff : forall a b, b~=0 -> (a/b==0 <-> a<b).
Proof. intros. apply div_small_iff; auto'. Qed.

Lemma mod_small_iff : forall a b, b~=0 -> (a mod b == a <-> a<b).
Proof. intros. apply mod_small_iff; auto'. Qed.

Lemma div_str_pos_iff : forall a b, b~=0 -> (0<a/b <-> b<=a).
Proof. intros. apply div_str_pos_iff; auto'. Qed.


(** As soon as the divisor is strictly greater than 1,
    the division is strictly decreasing. *)

Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof. exact div_lt. Qed.

(** [le] is compatible with a positive division. *)

Lemma div_le_mono : forall a b c, c~=0 -> a<=b -> a/c <= b/c.
Proof. intros. apply div_le_mono; auto'. Qed.

Lemma mul_div_le : forall a b, b~=0 -> b*(a/b) <= a.
Proof. intros. apply mul_div_le; auto'. Qed.

Lemma mul_succ_div_gt: forall a b, b~=0 -> a < b*(S (a/b)).
Proof. intros; apply mul_succ_div_gt; auto'. Qed.

(** The previous inequality is exact iff the modulo is zero. *)

Lemma div_exact : forall a b, b~=0 -> (a == b*(a/b) <-> a mod b == 0).
Proof. intros. apply div_exact; auto'. Qed.

(** Some additional inequalities about div. *)

Theorem div_lt_upper_bound:
  forall a b q, b~=0 -> a < b*q -> a/b < q.
Proof. intros. apply div_lt_upper_bound; auto'. Qed.

Theorem div_le_upper_bound:
  forall a b q, b~=0 -> a <= b*q -> a/b <= q.
Proof. intros; apply div_le_upper_bound; auto'. Qed.

Theorem div_le_lower_bound:
  forall a b q, b~=0 -> b*q <= a -> q <= a/b.
Proof. intros; apply div_le_lower_bound; auto'. Qed.

(** A division respects opposite monotonicity for the divisor *)

Lemma div_le_compat_l: forall p q r, 0<q<=r -> p/r <= p/q.
Proof. intros. apply div_le_compat_l. auto'. auto. Qed.

(** * Relations between usual operations and mod and div *)

Lemma mod_add : forall a b c, c~=0 ->
 (a + b * c) mod c == a mod c.
Proof. intros. apply mod_add; auto'. Qed.

Lemma div_add : forall a b c, c~=0 ->
 (a + b * c) / c == a / c + b.
Proof. intros. apply div_add; auto'. Qed.

Lemma div_add_l: forall a b c, b~=0 ->
 (a * b + c) / b == a + c / b.
Proof. intros. apply div_add_l; auto'. Qed.

(** Cancellations. *)

Lemma div_mul_cancel_r : forall a b c, b~=0 -> c~=0 ->
 (a*c)/(b*c) == a/b.
Proof. intros. apply div_mul_cancel_r; auto'. Qed.

Lemma div_mul_cancel_l : forall a b c, b~=0 -> c~=0 ->
 (c*a)/(c*b) == a/b.
Proof. intros. apply div_mul_cancel_l; auto'. Qed.

Lemma mul_mod_distr_r: forall a b c, b~=0 -> c~=0 ->
  (a*c) mod (b*c) == (a mod b) * c.
Proof. intros. apply mul_mod_distr_r; auto'. Qed.

Lemma mul_mod_distr_l: forall a b c, b~=0 -> c~=0 ->
  (c*a) mod (c*b) == c * (a mod b).
Proof. intros. apply mul_mod_distr_l; auto'. Qed.

(** Operations modulo. *)

Theorem mod_mod: forall a n, n~=0 ->
 (a mod n) mod n == a mod n.
Proof. intros. apply mod_mod; auto'. Qed.

Lemma mul_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)*b) mod n == (a*b) mod n.
Proof. intros. apply mul_mod_idemp_l; auto'. Qed.

Lemma mul_mod_idemp_r : forall a b n, n~=0 ->
 (a*(b mod n)) mod n == (a*b) mod n.
Proof. intros. apply mul_mod_idemp_r; auto'. Qed.

Theorem mul_mod: forall a b n, n~=0 ->
 (a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof. intros. apply mul_mod; auto'. Qed.

Lemma add_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)+b) mod n == (a+b) mod n.
Proof. intros. apply add_mod_idemp_l; auto'. Qed.

Lemma add_mod_idemp_r : forall a b n, n~=0 ->
 (a+(b mod n)) mod n == (a+b) mod n.
Proof. intros. apply add_mod_idemp_r; auto'. Qed.

Theorem add_mod: forall a b n, n~=0 ->
 (a+b) mod n == (a mod n + b mod n) mod n.
Proof. intros. apply add_mod; auto'. Qed.

Lemma div_div : forall a b c, b~=0 -> c~=0 ->
 (a/b)/c == a/(b*c).
Proof. intros. apply div_div; auto'. Qed.

Lemma mod_mul_r : forall a b c, b~=0 -> c~=0 ->
 a mod (b*c) == a mod b + b*((a/b) mod c).
Proof. intros. apply mod_mul_r; auto'. Qed.

(** A last inequality: *)

Theorem div_mul_le:
 forall a b c, b~=0 -> c*(a/b) <= (c*a)/b.
Proof. intros. apply div_mul_le; auto'. Qed.

(** mod is related to divisibility *)

Lemma mod_divides : forall a b, b~=0 ->
 (a mod b == 0 <-> exists c, a == b*c).
Proof. intros. apply mod_divides; auto'. Qed.

End NDivProp.
