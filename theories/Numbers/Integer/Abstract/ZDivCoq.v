(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Euclidean Division for integers

    We use here the historical convention of Coq :
    [a = bq+r /\ 0 < |r| < |b| /\ Sign(r) = Sgn(b)]
 *)

Require Import ZAxioms ZProperties NZDiv.

Open Scope NumScope.

Module Type ZDiv (Import Z : ZAxiomsSig).

 Parameter Inline div : t -> t -> t.
 Parameter Inline modulo : t -> t -> t.

 Infix "/" := div : NumScope.
 Infix "mod" := modulo (at level 40, no associativity) : NumScope.

 Instance div_wd : Proper (eq==>eq==>eq) div.
 Instance mod_wd : Proper (eq==>eq==>eq) modulo.

 Axiom div_mod : forall a b, b ~= 0 -> a == b*(a/b) + (a mod b).
 Axiom mod_pos_bound : forall a b, 0 < b -> 0 <= a mod b < b.
 Axiom mod_neg_bound : forall a b, b < 0 -> b < a mod b <= 0.

End ZDiv.

Module Type ZDivSig := ZAxiomsSig <+ ZDiv.

Module ZDivPropFunct (Import Z : ZDivSig).
 (* TODO: en faire un arg du foncteur + comprendre le bug de SearchAbout *)
 Module Import ZP := ZPropFunct Z.

(** We benefit from what already exists for NZ *)

 Module Z' <: NZDivSig.
  Include Z.
  Lemma mod_bound : forall a b, 0<=a -> 0<b -> 0 <= a mod b < b.
  Proof. intros; apply mod_pos_bound; auto. Qed.
 End Z'.
 Module Import NZDivP := NZDivPropFunct Z'.

(** Another formulation of the main equation *)

Lemma mod_eq :
 forall a b, b~=0 -> a mod b == a - b*(a/b).
Proof.
intros.
rewrite <- add_move_l.
symmetry. apply div_mod; auto.
Qed.

(** A few sign rules (simple ones) *)

Lemma div_mod_opp_opp : forall a b, b~=0 ->
 (-a/-b) == a/b /\ (-a) mod (-b) == -(a mod b).
Proof.
intros a b Hb.
assert (-b ~= 0).
 contradict Hb. rewrite eq_opp_l, opp_0 in Hb; auto.
assert (EQ := opp_involutive a).
rewrite (div_mod a b) in EQ at 2; auto.
rewrite (div_mod (-a) (-b)) in EQ; auto.

destruct (lt_ge_cases 0 b).
rewrite opp_add_distr in EQ.
rewrite <- mul_opp_l, opp_involutive in EQ.
destruct (div_mod_unique b (-a/-b) (a/b) (-(-a mod -b)) (a mod b)); auto.
rewrite <- (opp_involutive b) at 3.
rewrite <- opp_lt_mono.
rewrite opp_nonneg_nonpos.
destruct (mod_neg_bound (-a) (-b)); auto.
rewrite opp_neg_pos; auto.
apply mod_pos_bound; auto.
split; auto.
rewrite eq_opp_r; auto.

rewrite eq_opp_l in EQ.
rewrite opp_add_distr in EQ.
rewrite <- mul_opp_l in EQ.
destruct (div_mod_unique (-b) (-a/-b) (a/b) (-a mod -b) (-(a mod b))); auto.
apply mod_pos_bound; auto.
rewrite opp_pos_neg; order.
rewrite <- opp_lt_mono.
rewrite opp_nonneg_nonpos.
destruct (mod_neg_bound a b); intuition; order.
Qed.

Lemma div_opp_opp : forall a b, b~=0 -> -a/-b == a/b.
Proof.
intros; destruct (div_mod_opp_opp a b); auto.
Qed.

Lemma mod_opp_opp : forall a b, b~=0 -> (-a) mod (-b) == - (a mod b).
Proof.
intros; destruct (div_mod_opp_opp a b); auto.
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
 forall a b q r, (0<=r<b \/ b<r<=0) -> a == b*q + r -> q == a/b.
Proof.
intros a b q r Hr EQ.
assert (Hb : b~=0) by (destruct Hr; intuition; order).
rewrite (div_mod a b Hb) in EQ.
destruct (div_mod_unique b (a/b) q (a mod b) r); auto.
destruct Hr; [left; apply mod_pos_bound|right; apply mod_neg_bound];
 intuition order.
Qed.

Theorem div_unique_pos:
 forall a b q r, 0<=r<b -> a == b*q + r -> q == a/b.
Proof. intros; apply div_unique with r; auto. Qed.

Theorem div_unique_neg:
 forall a b q r, 0<=r<b -> a == b*q + r -> q == a/b.
Proof. intros; apply div_unique with r; auto. Qed.

Theorem mod_unique:
 forall a b q r, (0<=r<b \/ b<r<=0) -> a == b*q + r -> r == a mod b.
Proof.
intros a b q r Hr EQ.
assert (Hb : b~=0) by (destruct Hr; intuition; order).
rewrite (div_mod a b Hb) in EQ.
destruct (div_mod_unique b (a/b) q (a mod b) r); auto.
destruct Hr; [left; apply mod_pos_bound|right; apply mod_neg_bound];
 intuition order.
Qed.

Theorem mod_unique_pos:
 forall a b q r, 0<=r<b -> a == b*q + r -> r == a mod b.
Proof. intros; apply mod_unique with q; auto. Qed.

Theorem mod_unique_neg:
 forall a b q r, b<r<=0 -> a == b*q + r -> r == a mod b.
Proof. intros; apply mod_unique with q; auto. Qed.


(** A division by itself returns 1 *)

Ltac pos_or_neg a :=
 let LT := fresh "LT" in
 let LE := fresh "LE" in 
 destruct (le_gt_cases 0 a) as [LE|LT]; [|rewrite <- opp_pos_neg in LT].

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
intros. symmetry. apply div_unique with 0. left. split; order || apply lt_0_1.
nzsimpl; auto.
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

(* A REVOIR APRES LA REGLE DES SIGNES
Lemma div_small_iff : forall a b, b~=0 -> (a/b==0 <-> 0<=a<b \/ b<a<=0).
intros. apply div_small_iff; auto'. Qed.

Lemma mod_small_iff : forall a b, b~=0 -> (a mod b == a <-> a<b).
Proof. intros. apply mod_small_iff; auto'. Qed.

Lemma div_str_pos_iff : forall a b, b~=0 -> (0<a/b <-> b<=a).
Proof. intros. apply div_str_pos_iff; auto'. Qed.
*)

(** As soon as the divisor is strictly greater than 1,
    the division is strictly decreasing. *)

Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof. exact div_lt. Qed.

(* STILL TODO !!

(** [le] is compatible with a positive division. *)

Lemma div_le_mono : forall a b c, 0<c -> a<=b -> a/c <= b/c.
Proof.
intros. destruct (le_gt_cases 0 a).
apply div_le; auto.
destruct (lt_ge_cases 0 b).
apply le_trans with 0.
 admit. (* !!! *)
apply div_pos; order.
Admitted. (* !!! *)

Lemma mul_div_le : forall a b, b~=0 -> b*(a/b) <= a.
Proof. intros. apply mul_div_le; auto'. Qed.

Lemma mul_succ_div_gt: forall a b, b~=0 -> a < b*(S (a/b)).
Proof. intros; apply mul_succ_div_gt; auto'. Qed.

(** The previous inequality is exact iff the modulo is zero. *)

Lemma div_exact : forall a b, b~=0 -> (a == b*(a/b) <-> a mod b == 0).
Proof. intros. apply div_exact; auto'. Qed.

(** Some additionnal inequalities about div. *)

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

Lemma div_le_compat_l: forall p q r, 0<q<r -> p/r <= p/q.
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

Lemma mul_mod_distr_l: forall a b c, b~=0 -> c~=0 ->
  (c*a) mod (c*b) == c * (a mod b).
Proof. intros. apply mul_mod_distr_l; auto'. Qed.

Lemma mul_mod_distr_r: forall a b c, b~=0 -> c~=0 ->
  (a*c) mod (b*c) == (a mod b) * c.
Proof. intros. apply mul_mod_distr_r; auto'. Qed.

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

(** A last inequality: *)

Theorem div_mul_le:
 forall a b c, b~=0 -> c*(a/b) <= (c*a)/b.
Proof. intros. apply div_mul_le; auto'. Qed.

(** mod is related to divisibility *)

Lemma mod_divides : forall a b, b~=0 ->
 (a mod b == 0 <-> exists c, a == b*c).
Proof. intros. apply mod_divides; auto'. Qed.
*)

End ZDivPropFunct.

