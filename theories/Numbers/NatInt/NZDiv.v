(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Euclidean Division *)

Require Import NZAxioms NZMulOrder.

(** The first signatures will be common to all divisions over NZ, N and Z *)

Module Type DivMod (Import A : Typ).
 Parameters Inline div modulo : t -> t -> t.
End DivMod.

Module Type DivModNotation (A : Typ)(Import B : DivMod A).
 Infix "/" := div.
 Infix "mod" := modulo (at level 40, no associativity).
End DivModNotation.

Module Type DivMod' (A : Typ) := DivMod A <+ DivModNotation A.

Module Type NZDivSpec (Import A : NZOrdAxiomsSig')(Import B : DivMod' A).
 Declare Instance div_wd : Proper (eq==>eq==>eq) div.
 Declare Instance mod_wd : Proper (eq==>eq==>eq) modulo.
 Axiom div_mod : forall a b, b ~= 0 -> a == b*(a/b) + (a mod b).
 Axiom mod_bound_pos : forall a b, 0<=a -> 0<b -> 0 <= a mod b < b.
End NZDivSpec.

(** The different divisions will only differ in the conditions
    they impose on [modulo]. For NZ, we have only described the
    behavior on positive numbers.
*)

Module Type NZDiv (A : NZOrdAxiomsSig) := DivMod A <+ NZDivSpec A.
Module Type NZDiv' (A : NZOrdAxiomsSig) := NZDiv A <+ DivModNotation A.

Module Type NZDivProp
 (Import A : NZOrdAxiomsSig')
 (Import B : NZDiv' A)
 (Import C : NZMulOrderProp A).

(** Uniqueness theorems *)

Theorem div_mod_unique :
 forall b q1 q2 r1 r2, 0<=r1<b -> 0<=r2<b ->
  b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof.
intros b.
assert (U : forall q1 q2 r1 r2,
            b*q1+r1 == b*q2+r2 -> 0<=r1<b -> 0<=r2 -> q1<q2 -> False).
 intros q1 q2 r1 r2 EQ LT Hr1 Hr2.
 contradict EQ.
 apply lt_neq.
 apply lt_le_trans with (b*q1+b).
 rewrite <- add_lt_mono_l. tauto.
 apply le_trans with (b*q2).
 rewrite mul_comm, <- mul_succ_l, mul_comm.
 apply mul_le_mono_nonneg_l; intuition; try order.
 rewrite le_succ_l; auto.
 rewrite <- (add_0_r (b*q2)) at 1.
 rewrite <- add_le_mono_l. tauto.

intros q1 q2 r1 r2 Hr1 Hr2 EQ; destruct (lt_trichotomy q1 q2) as [LT|[EQ'|GT]].
elim (U q1 q2 r1 r2); intuition.
split; auto. rewrite EQ' in EQ. rewrite add_cancel_l in EQ; auto.
elim (U q2 q1 r2 r1); intuition.
Qed.

Theorem div_unique:
 forall a b q r, 0<=a -> 0<=r<b ->
   a == b*q + r -> q == a/b.
Proof.
intros a b q r Ha (Hb,Hr) EQ.
destruct (div_mod_unique b q (a/b) r (a mod b)); auto.
apply mod_bound_pos; order.
rewrite <- div_mod; order.
Qed.

Theorem mod_unique:
 forall a b q r, 0<=a -> 0<=r<b ->
  a == b*q + r -> r == a mod b.
Proof.
intros a b q r Ha (Hb,Hr) EQ.
destruct (div_mod_unique b q (a/b) r (a mod b)); auto.
apply mod_bound_pos; order.
rewrite <- div_mod; order.
Qed.

Theorem div_unique_exact a b q:
 0<=a -> 0<b -> a == b*q -> q == a/b.
Proof.
 intros Ha Hb H. apply div_unique with 0; nzsimpl; now try split.
Qed.

(** A division by itself returns 1 *)

Lemma div_same : forall a, 0<a -> a/a == 1.
Proof.
intros. symmetry. apply div_unique_exact; nzsimpl; order.
Qed.

Lemma mod_same : forall a, 0<a -> a mod a == 0.
Proof.
intros. symmetry.
apply mod_unique with 1; intuition; try order.
now nzsimpl.
Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem div_small: forall a b, 0<=a<b -> a/b == 0.
Proof.
intros. symmetry.
apply div_unique with a; intuition; try order.
now nzsimpl.
Qed.

(** Same situation, in term of modulo: *)

Theorem mod_small: forall a b, 0<=a<b -> a mod b == a.
Proof.
intros. symmetry.
apply mod_unique with 0; intuition; try order.
now nzsimpl.
Qed.

(** * Basic values of divisions and modulo. *)

Lemma div_0_l: forall a, 0<a -> 0/a == 0.
Proof.
intros; apply div_small; split; order.
Qed.

Lemma mod_0_l: forall a, 0<a -> 0 mod a == 0.
Proof.
intros; apply mod_small; split; order.
Qed.

Lemma div_1_r: forall a, 0<=a -> a/1 == a.
Proof.
intros. symmetry. apply div_unique_exact; nzsimpl; order'.
Qed.

Lemma mod_1_r: forall a, 0<=a -> a mod 1 == 0.
Proof.
intros. symmetry.
apply mod_unique with a; try split; try order; try apply lt_0_1.
now nzsimpl.
Qed.

Lemma div_1_l: forall a, 1<a -> 1/a == 0.
Proof.
intros; apply div_small; split; auto. apply le_0_1.
Qed.

Lemma mod_1_l: forall a, 1<a -> 1 mod a == 1.
Proof.
intros; apply mod_small; split; auto. apply le_0_1.
Qed.

Lemma div_mul : forall a b, 0<=a -> 0<b -> (a*b)/b == a.
Proof.
intros; symmetry. apply div_unique_exact; trivial.
apply mul_nonneg_nonneg; order.
apply mul_comm.
Qed.

Lemma mod_mul : forall a b, 0<=a -> 0<b -> (a*b) mod b == 0.
Proof.
intros; symmetry.
apply mod_unique with a; try split; try order.
apply mul_nonneg_nonneg; order.
nzsimpl; apply mul_comm.
Qed.


(** * Order results about mod and div *)

(** A modulo cannot grow beyond its starting point. *)

Theorem mod_le: forall a b, 0<=a -> 0<b -> a mod b <= a.
Proof.
intros. destruct (le_gt_cases b a).
apply le_trans with b; auto.
apply lt_le_incl. destruct (mod_bound_pos a b); auto.
rewrite lt_eq_cases; right.
apply mod_small; auto.
Qed.


(* Division of positive numbers is positive. *)

Lemma div_pos: forall a b, 0<=a -> 0<b -> 0 <= a/b.
Proof.
intros.
rewrite (mul_le_mono_pos_l _ _ b); auto; nzsimpl.
rewrite (add_le_mono_r _ _ (a mod b)).
rewrite <- div_mod by order.
nzsimpl.
apply mod_le; auto.
Qed.

Lemma div_str_pos : forall a b, 0<b<=a -> 0 < a/b.
Proof.
intros a b (Hb,Hab).
assert (LE : 0 <= a/b) by (apply div_pos; order).
assert (MOD : a mod b < b) by (destruct (mod_bound_pos a b); order).
rewrite lt_eq_cases in LE; destruct LE as [LT|EQ]; auto.
exfalso; revert Hab.
rewrite (div_mod a b), <-EQ; nzsimpl; order.
Qed.

Lemma div_small_iff : forall a b, 0<=a -> 0<b -> (a/b==0 <-> a<b).
Proof.
intros a b Ha Hb; split; intros Hab.
destruct (lt_ge_cases a b); auto.
symmetry in Hab. contradict Hab. apply lt_neq, div_str_pos; auto.
apply div_small; auto.
Qed.

Lemma mod_small_iff : forall a b, 0<=a -> 0<b -> (a mod b == a <-> a<b).
Proof.
intros a b Ha Hb. split; intros H; auto using mod_small.
rewrite <- div_small_iff; auto.
rewrite <- (mul_cancel_l _ _ b) by order.
rewrite <- (add_cancel_r _ _ (a mod b)).
rewrite <- div_mod, H by order. now nzsimpl.
Qed.

Lemma div_str_pos_iff : forall a b, 0<=a -> 0<b -> (0<a/b <-> b<=a).
Proof.
intros a b Ha Hb; split; intros Hab.
destruct (lt_ge_cases a b) as [LT|LE]; auto.
rewrite <- div_small_iff in LT; order.
apply div_str_pos; auto.
Qed.


(** As soon as the divisor is strictly greater than 1,
    the division is strictly decreasing. *)

Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof.
intros.
assert (0 < b) by (apply lt_trans with 1; auto using lt_0_1).
destruct (lt_ge_cases a b).
rewrite div_small; try split; order.
rewrite (div_mod a b) at 2 by order.
apply lt_le_trans with (b*(a/b)).
rewrite <- (mul_1_l (a/b)) at 1.
rewrite <- mul_lt_mono_pos_r; auto.
apply div_str_pos; auto.
rewrite <- (add_0_r (b*(a/b))) at 1.
rewrite <- add_le_mono_l. destruct (mod_bound_pos a b); order.
Qed.

(** [le] is compatible with a positive division. *)

Lemma div_le_mono : forall a b c, 0<c -> 0<=a<=b -> a/c <= b/c.
Proof.
intros a b c Hc (Ha,Hab).
rewrite lt_eq_cases in Hab. destruct Hab as [LT|EQ];
 [|rewrite EQ; order].
rewrite <- lt_succ_r.
rewrite (mul_lt_mono_pos_l c) by order.
nzsimpl.
rewrite (add_lt_mono_r _ _ (a mod c)).
rewrite <- div_mod by order.
apply lt_le_trans with b; auto.
rewrite (div_mod b c) at 1 by order.
rewrite <- add_assoc, <- add_le_mono_l.
apply le_trans with (c+0).
nzsimpl; destruct (mod_bound_pos b c); order.
rewrite <- add_le_mono_l. destruct (mod_bound_pos a c); order.
Qed.

(** The following two properties could be used as specification of div *)

Lemma mul_div_le : forall a b, 0<=a -> 0<b -> b*(a/b) <= a.
Proof.
intros.
rewrite (add_le_mono_r _ _ (a mod b)), <- div_mod by order.
rewrite <- (add_0_r a) at 1.
rewrite <- add_le_mono_l. destruct (mod_bound_pos a b); order.
Qed.

Lemma mul_succ_div_gt : forall a b, 0<=a -> 0<b -> a < b*(S (a/b)).
Proof.
intros.
rewrite (div_mod a b) at 1 by order.
rewrite (mul_succ_r).
rewrite <- add_lt_mono_l.
destruct (mod_bound_pos a b); auto.
Qed.


(** The previous inequality is exact iff the modulo is zero. *)

Lemma div_exact : forall a b, 0<=a -> 0<b -> (a == b*(a/b) <-> a mod b == 0).
Proof.
intros. rewrite (div_mod a b) at 1 by order.
rewrite <- (add_0_r (b*(a/b))) at 2.
apply add_cancel_l.
Qed.

(** Some additional inequalities about div. *)

Theorem div_lt_upper_bound:
  forall a b q, 0<=a -> 0<b -> a < b*q -> a/b < q.
Proof.
intros.
rewrite (mul_lt_mono_pos_l b) by order.
apply le_lt_trans with a; auto.
apply mul_div_le; auto.
Qed.

Theorem div_le_upper_bound:
  forall a b q, 0<=a -> 0<b -> a <= b*q -> a/b <= q.
Proof.
intros.
rewrite (mul_le_mono_pos_l _ _ b) by order.
apply le_trans with a; auto.
apply mul_div_le; auto.
Qed.

Theorem div_le_lower_bound:
  forall a b q, 0<=a -> 0<b -> b*q <= a -> q <= a/b.
Proof.
intros a b q Ha Hb H.
destruct (lt_ge_cases 0 q).
rewrite <- (div_mul q b); try order.
apply div_le_mono; auto.
rewrite mul_comm; split; auto.
apply lt_le_incl, mul_pos_pos; auto.
apply le_trans with 0; auto; apply div_pos; auto.
Qed.

(** A division respects opposite monotonicity for the divisor *)

Lemma div_le_compat_l: forall p q r, 0<=p -> 0<q<=r ->
    p/r <= p/q.
Proof.
 intros p q r Hp (Hq,Hqr).
 apply div_le_lower_bound; auto.
 rewrite (div_mod p r) at 2 by order.
 apply le_trans with (r*(p/r)).
 apply mul_le_mono_nonneg_r; try order.
 apply div_pos; order.
 rewrite <- (add_0_r (r*(p/r))) at 1.
 rewrite <- add_le_mono_l. destruct (mod_bound_pos p r); order.
Qed.


(** * Relations between usual operations and mod and div *)

Lemma mod_add : forall a b c, 0<=a -> 0<=a+b*c -> 0<c ->
 (a + b * c) mod c == a mod c.
Proof.
 intros.
 symmetry.
 apply mod_unique with (a/c+b); auto.
 apply mod_bound_pos; auto.
 rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
 now rewrite mul_comm.
Qed.

Lemma div_add : forall a b c, 0<=a -> 0<=a+b*c -> 0<c ->
 (a + b * c) / c == a / c + b.
Proof.
 intros.
 apply (mul_cancel_l _ _ c); try order.
 apply (add_cancel_r _ _ ((a+b*c) mod c)).
 rewrite <- div_mod, mod_add by order.
 rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
 now rewrite mul_comm.
Qed.

Lemma div_add_l: forall a b c, 0<=c -> 0<=a*b+c -> 0<b ->
 (a * b + c) / b == a + c / b.
Proof.
 intros a b c. rewrite (add_comm _ c), (add_comm a).
 intros. apply div_add; auto.
Qed.

(** Cancellations. *)

Lemma div_mul_cancel_r : forall a b c, 0<=a -> 0<b -> 0<c ->
 (a*c)/(b*c) == a/b.
Proof.
 intros.
 symmetry.
 apply div_unique with ((a mod b)*c).
 apply mul_nonneg_nonneg; order.
 split.
 apply mul_nonneg_nonneg; destruct (mod_bound_pos a b); order.
 rewrite <- mul_lt_mono_pos_r; auto. destruct (mod_bound_pos a b); auto.
 rewrite (div_mod a b) at 1 by order.
 rewrite mul_add_distr_r.
 rewrite add_cancel_r.
 rewrite <- 2 mul_assoc. now rewrite (mul_comm c).
Qed.

Lemma div_mul_cancel_l : forall a b c, 0<=a -> 0<b -> 0<c ->
 (c*a)/(c*b) == a/b.
Proof.
 intros. rewrite !(mul_comm c); apply div_mul_cancel_r; auto.
Qed.

Lemma mul_mod_distr_l: forall a b c, 0<=a -> 0<b -> 0<c ->
  (c*a) mod (c*b) == c * (a mod b).
Proof.
 intros.
 rewrite <- (add_cancel_l _ _ ((c*b)* ((c*a)/(c*b)))).
 rewrite <- div_mod.
 rewrite div_mul_cancel_l; auto.
 rewrite <- mul_assoc, <- mul_add_distr_l, mul_cancel_l by order.
 apply div_mod; order.
 rewrite <- neq_mul_0; intuition; order.
Qed.

Lemma mul_mod_distr_r: forall a b c, 0<=a -> 0<b -> 0<c ->
  (a*c) mod (b*c) == (a mod b) * c.
Proof.
 intros. rewrite !(mul_comm _ c); now rewrite mul_mod_distr_l.
Qed.

(** Operations modulo. *)

Theorem mod_mod: forall a n, 0<=a -> 0<n ->
 (a mod n) mod n == a mod n.
Proof.
 intros. destruct (mod_bound_pos a n); auto. now rewrite mod_small_iff.
Qed.

Lemma mul_mod_idemp_l : forall a b n, 0<=a -> 0<=b -> 0<n ->
 ((a mod n)*b) mod n == (a*b) mod n.
Proof.
 intros a b n Ha Hb Hn. symmetry.
 generalize (mul_nonneg_nonneg _ _ Ha Hb).
 rewrite (div_mod a n) at 1 2 by order.
 rewrite add_comm, (mul_comm n), (mul_comm _ b).
 rewrite mul_add_distr_l, mul_assoc.
 intros. rewrite mod_add; auto.
 now rewrite mul_comm.
 apply mul_nonneg_nonneg; destruct (mod_bound_pos a n); auto.
Qed.

Lemma mul_mod_idemp_r : forall a b n, 0<=a -> 0<=b -> 0<n ->
 (a*(b mod n)) mod n == (a*b) mod n.
Proof.
 intros. rewrite !(mul_comm a). apply mul_mod_idemp_l; auto.
Qed.

Theorem mul_mod: forall a b n, 0<=a -> 0<=b -> 0<n ->
 (a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof.
 intros. rewrite mul_mod_idemp_l, mul_mod_idemp_r; trivial. reflexivity.
 now destruct (mod_bound_pos b n).
Qed.

Lemma add_mod_idemp_l : forall a b n, 0<=a -> 0<=b -> 0<n ->
 ((a mod n)+b) mod n == (a+b) mod n.
Proof.
 intros a b n Ha Hb Hn. symmetry.
 generalize (add_nonneg_nonneg _ _ Ha Hb).
 rewrite (div_mod a n) at 1 2 by order.
 rewrite <- add_assoc, add_comm, mul_comm.
 intros. rewrite mod_add; trivial. reflexivity.
 apply add_nonneg_nonneg; auto. destruct (mod_bound_pos a n); auto.
Qed.

Lemma add_mod_idemp_r : forall a b n, 0<=a -> 0<=b -> 0<n ->
 (a+(b mod n)) mod n == (a+b) mod n.
Proof.
 intros. rewrite !(add_comm a). apply add_mod_idemp_l; auto.
Qed.

Theorem add_mod: forall a b n, 0<=a -> 0<=b -> 0<n ->
 (a+b) mod n == (a mod n + b mod n) mod n.
Proof.
 intros. rewrite add_mod_idemp_l, add_mod_idemp_r; trivial. reflexivity.
 now destruct (mod_bound_pos b n).
Qed.

Lemma div_div : forall a b c, 0<=a -> 0<b -> 0<c ->
 (a/b)/c == a/(b*c).
Proof.
 intros a b c Ha Hb Hc.
 apply div_unique with (b*((a/b) mod c) + a mod b); trivial.
 (* begin 0<= ... <b*c *)
 destruct (mod_bound_pos (a/b) c), (mod_bound_pos a b); auto using div_pos.
 split.
 apply add_nonneg_nonneg; auto.
 apply mul_nonneg_nonneg; order.
 apply lt_le_trans with (b*((a/b) mod c) + b).
 rewrite <- add_lt_mono_l; auto.
 rewrite <- mul_succ_r, <- mul_le_mono_pos_l, le_succ_l; auto.
 (* end 0<= ... < b*c *)
 rewrite (div_mod a b) at 1 by order.
 rewrite add_assoc, add_cancel_r.
 rewrite <- mul_assoc, <- mul_add_distr_l, mul_cancel_l by order.
 apply div_mod; order.
Qed.

Lemma mod_mul_r : forall a b c, 0<=a -> 0<b -> 0<c ->
 a mod (b*c) == a mod b + b*((a/b) mod c).
Proof.
 intros a b c Ha Hb Hc.
 apply add_cancel_l with (b*c*(a/(b*c))).
 rewrite <- div_mod by (apply neq_mul_0; split; order).
 rewrite <- div_div by trivial.
 rewrite add_assoc, add_shuffle0, <- mul_assoc, <- mul_add_distr_l.
 rewrite <- div_mod by order.
 apply div_mod; order.
Qed.

(** A last inequality: *)

Theorem div_mul_le:
 forall a b c, 0<=a -> 0<b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof.
 intros.
 apply div_le_lower_bound; auto.
 apply mul_nonneg_nonneg; auto.
 rewrite mul_assoc, (mul_comm b c), <- mul_assoc.
 apply mul_le_mono_nonneg_l; auto.
 apply mul_div_le; auto.
Qed.

(** mod is related to divisibility *)

Lemma mod_divides : forall a b, 0<=a -> 0<b ->
 (a mod b == 0 <-> exists c, a == b*c).
Proof.
 split.
 intros. exists (a/b). rewrite div_exact; auto.
 intros (c,Hc). rewrite Hc, mul_comm. apply mod_mul; auto.
 rewrite (mul_le_mono_pos_l _ _ b); auto. nzsimpl. order.
Qed.

End NZDivProp.

