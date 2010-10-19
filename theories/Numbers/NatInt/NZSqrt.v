(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Square Root Function *)

Require Import NZAxioms NZMulOrder.

(** Interface of a sqrt function, then its specification on naturals *)

Module Type Sqrt (Import T:Typ).
 Parameters Inline sqrt : t -> t.
End Sqrt.

Module Type SqrtNotation (T:Typ)(Import NZ:Sqrt T).
 Notation "√ x" := (sqrt x) (at level 25).
End SqrtNotation.

Module Type Sqrt' (T:Typ) := Sqrt T <+ SqrtNotation T.

Module Type NZSqrtSpec (Import NZ : NZOrdAxiomsSig')(Import P : Sqrt' NZ).
 Declare Instance sqrt_wd : Proper (eq==>eq) sqrt.
 Axiom sqrt_spec : forall a, 0<=a -> √a * √a <= a < S (√a) * S (√a).
End NZSqrtSpec.

Module Type NZSqrt (NZ:NZOrdAxiomsSig) := Sqrt NZ <+ NZSqrtSpec NZ.
Module Type NZSqrt' (NZ:NZOrdAxiomsSig) := Sqrt' NZ <+ NZSqrtSpec NZ.

(** Derived properties of power *)

Module NZSqrtProp
 (Import NZ : NZOrdAxiomsSig')
 (Import NZP' : NZSqrt' NZ)
 (Import NZP : NZMulOrderProp NZ).

(** First, sqrt is non-negative *)

Lemma sqrt_spec_nonneg : forall a b, 0<=a ->
 b*b <= a < S b * S b -> 0 <= b.
Proof.
 intros a b Ha (LE,LT).
 destruct (le_gt_cases 0 b) as [Hb|Hb]; trivial. exfalso.
 assert (S b * S b < b * b).
  rewrite mul_succ_l, <- (add_0_r (b*b)).
  apply add_lt_le_mono.
  apply mul_lt_mono_neg_l; trivial. apply lt_succ_diag_r.
  now apply le_succ_l.
 order.
Qed.

Lemma sqrt_nonneg : forall a, 0<=a -> 0<=√a.
Proof.
 intros. now apply (sqrt_spec_nonneg a), sqrt_spec.
Qed.

(** The spec of sqrt indeed determines it *)

Lemma sqrt_unique : forall a b, 0<=a -> b*b<=a<(S b)*(S b) -> √a == b.
Proof.
 intros a b Ha (LEb,LTb).
 assert (0<=b) by (apply (sqrt_spec_nonneg a); try split; trivial).
 assert (0<=√a) by now apply sqrt_nonneg.
 destruct (sqrt_spec a Ha) as (LEa,LTa).
 assert (b <= √a).
  apply lt_succ_r, square_lt_simpl_nonneg; [|order].
  now apply lt_le_incl, lt_succ_r.
 assert (√a <= b).
  apply lt_succ_r, square_lt_simpl_nonneg; [|order].
  now apply lt_le_incl, lt_succ_r.
 order.
Qed.

(** Sqrt is exact on squares *)

Lemma sqrt_square : forall a, 0<=a -> √(a*a) == a.
Proof.
 intros a Ha.
 apply sqrt_unique.
 apply square_nonneg.
 split. order.
 apply mul_lt_mono_nonneg; trivial using lt_succ_diag_r.
Qed.

(** Sqrt is a monotone function (but not a strict one) *)

Lemma sqrt_le_mono : forall a b, 0<=a<=b -> √a <= √b.
Proof.
 intros a b (Ha,Hab).
 assert (Hb : 0 <= b) by order.
 destruct (sqrt_spec a Ha) as (LE,_).
 destruct (sqrt_spec b Hb) as (_,LT).
 apply lt_succ_r.
 apply square_lt_simpl_nonneg; try order.
 now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
Qed.

(** No reverse result for <=, consider for instance √2 <= √1 *)

Lemma sqrt_lt_cancel : forall a b, 0<=a -> 0<=b -> √a < √b -> a < b.
Proof.
 intros a b Ha Hb H.
 destruct (sqrt_spec a Ha) as (_,LT).
 destruct (sqrt_spec b Hb) as (LE,_).
 apply le_succ_l in H.
 assert (S (√a) * S (√a) <= √b * √b).
  apply mul_le_mono_nonneg; trivial.
  now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
  now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
 order.
Qed.

(** When left side is a square, we have an equivalence for <= *)

Lemma sqrt_le_square : forall a b, 0<=a -> 0<=b -> (b*b<=a <-> b <= √a).
Proof.
 intros a b Ha Hb. split; intros H.
 rewrite <- (sqrt_square b); trivial.
 apply sqrt_le_mono. split. apply square_nonneg. trivial.
 destruct (sqrt_spec a Ha) as (LE,LT).
 transitivity (√a * √a); trivial.
 now apply mul_le_mono_nonneg.
Qed.

(** When right side is a square, we have an equivalence for < *)

Lemma sqrt_lt_square : forall a b, 0<=a -> 0<=b -> (a<b*b <-> √a < b).
Proof.
 intros a b Ha Hb. split; intros H.
 destruct (sqrt_spec a Ha) as (LE,_).
 apply square_lt_simpl_nonneg; try order.
 rewrite <- (sqrt_square b Hb) in H.
 apply sqrt_lt_cancel; trivial.
 apply square_nonneg.
Qed.

(** Sqrt and basic constants *)

Lemma sqrt_0 : √0 == 0.
Proof.
 rewrite <- (mul_0_l 0) at 1. now apply sqrt_square.
Qed.

Lemma sqrt_1 : √1 == 1.
Proof.
 rewrite <- (mul_1_l 1) at 1. apply sqrt_square. order'.
Qed.

Lemma sqrt_2 : √2 == 1.
Proof.
 apply sqrt_unique. order'. nzsimpl. split. order'.
 apply lt_succ_r, lt_le_incl, lt_succ_r. nzsimpl'; order.
Qed.

Lemma sqrt_lt_lin : forall a, 1<a -> √a<a.
Proof.
 intros a Ha. rewrite <- sqrt_lt_square; try order'.
 rewrite <- (mul_1_r a) at 1.
 rewrite <- mul_lt_mono_pos_l; order'.
Qed.

Lemma sqrt_le_lin : forall a, 0<=a -> √a<=a.
Proof.
 intros a Ha.
 destruct (le_gt_cases a 0) as [H|H].
 setoid_replace a with 0 by order. now rewrite sqrt_0.
 destruct (le_gt_cases a 1) as [H'|H'].
 rewrite <- le_succ_l, <- one_succ in H.
 setoid_replace a with 1 by order. now rewrite sqrt_1.
 now apply lt_le_incl, sqrt_lt_lin.
Qed.

(** Sqrt and multiplication. *)

(** Due to rounding error, we don't have the usual √(a*b) = √a*√b
    but only lower and upper bounds. *)

Lemma sqrt_mul_below : forall a b, 0<=a -> 0<=b -> √a * √b <= √(a*b).
Proof.
 intros a b Ha Hb.
 assert (Ha':=sqrt_nonneg _ Ha).
 assert (Hb':=sqrt_nonneg _ Hb).
 apply sqrt_le_square; try now apply mul_nonneg_nonneg.
 rewrite mul_shuffle1.
 apply mul_le_mono_nonneg; try now apply mul_nonneg_nonneg.
  now apply sqrt_spec.
  now apply sqrt_spec.
Qed.

Lemma sqrt_mul_above : forall a b, 0<=a -> 0<=b ->
 √(a*b) < S (√a) * S (√b).
Proof.
 intros a b Ha Hb.
 apply sqrt_lt_square.
 now apply mul_nonneg_nonneg.
 apply mul_nonneg_nonneg.
 now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
 now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
 rewrite mul_shuffle1.
 apply mul_lt_mono_nonneg; trivial; now apply sqrt_spec.
Qed.

(** And we can't find better approximations in general.
    - The lower bound is exact for squares
    - Concerning the upper bound, for any c>0, take a=b=c*c-1,
      then √(a*b) = c*c -1 while S √a = S √b = c
*)

(** Sqrt and addition *)

Lemma sqrt_add_le : forall a b, 0<=a -> 0<=b -> √(a+b) <= √a + √b.
Proof.
 intros a b Ha Hb.
 assert (Ha':=sqrt_nonneg _ Ha).
 assert (Hb':=sqrt_nonneg _ Hb).
 rewrite <- lt_succ_r.
 apply sqrt_lt_square.
  now apply add_nonneg_nonneg.
  now apply lt_le_incl, lt_succ_r, add_nonneg_nonneg.
 destruct (sqrt_spec a Ha) as (_,LTa).
 destruct (sqrt_spec b Hb) as (_,LTb).
 revert LTa LTb. nzsimpl. rewrite 3 lt_succ_r.
 intros LTa LTb.
 assert (H:=add_le_mono _ _ _ _ LTa LTb).
 etransitivity; [eexact H|]. clear LTa LTb H.
 rewrite <- (add_assoc _ (√a) (√a)).
 rewrite <- (add_assoc _ (√b) (√b)).
 rewrite add_shuffle1.
 rewrite <- (add_assoc _ (√a + √b)).
 rewrite (add_shuffle1 (√a) (√b)).
 apply add_le_mono_r.
 now apply add_square_le.
Qed.

(** convexity inequality for sqrt: sqrt of middle is above middle
    of square roots. *)

Lemma add_sqrt_le : forall a b, 0<=a -> 0<=b -> √a + √b <= √(2*(a+b)).
Proof.
 intros a b Ha Hb.
 assert (Ha':=sqrt_nonneg _ Ha).
 assert (Hb':=sqrt_nonneg _ Hb).
 apply sqrt_le_square.
  apply mul_nonneg_nonneg. order'. now apply add_nonneg_nonneg.
  now apply add_nonneg_nonneg.
 transitivity (2*(√a*√a + √b*√b)).
 now apply square_add_le.
 apply mul_le_mono_nonneg_l. order'.
 apply add_le_mono; now apply sqrt_spec.
Qed.

End NZSqrtProp.
