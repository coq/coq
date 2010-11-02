(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Base-2 Logarithm *)

Require Import NZAxioms NZMulOrder NZPow.

(** Interface of a log2 function, then its specification on naturals *)

Module Type Log2 (Import A : Typ).
 Parameters Inline log2 : t -> t.
End Log2.

Module Type NZLog2Spec (A : NZOrdAxiomsSig')(B : Pow' A)(C : Log2 A).
 Import A B C.
 Axiom log2_spec : forall a, 0<a -> 2^(log2 a) <= a < 2^(S (log2 a)).
 Axiom log2_nonpos : forall a, a<=0 -> log2 a == 0.
End NZLog2Spec.

Module Type NZLog2 (A : NZOrdAxiomsSig)(B : Pow A) := Log2 A <+ NZLog2Spec A B.

(** Derived properties of logarithm *)

Module NZLog2Prop
 (Import A : NZOrdAxiomsSig')
 (Import B : NZPow' A)
 (Import C : NZLog2 A B)
 (Import D : NZMulOrderProp A)
 (Import E : NZPowProp A B D).

(** log2 is always non-negative *)

Lemma log2_nonneg : forall a, 0 <= log2 a.
Proof.
 intros a. destruct (le_gt_cases a 0) as [Ha|Ha].
 now rewrite log2_nonpos.
 destruct (log2_spec a Ha) as (_,LT).
 apply lt_succ_r, (pow_gt_1 2). order'.
 rewrite <- le_succ_l, <- one_succ in Ha. order.
Qed.

(** A tactic for proving positivity and non-negativity *)

Ltac order_pos :=
((apply add_pos_pos || apply add_nonneg_nonneg ||
  apply mul_pos_pos || apply mul_nonneg_nonneg ||
  apply pow_nonneg || apply pow_pos_nonneg ||
  apply log2_nonneg || apply (le_le_succ_r 0));
 order_pos) (* in case of success of an apply, we recurse *)
|| order'.  (* otherwise *)

(** The spec of log2 indeed determines it *)

Lemma log2_unique : forall a b, 0<=b -> 2^b<=a<2^(S b) -> log2 a == b.
Proof.
 intros a b Hb (LEb,LTb).
 assert (Ha : 0 < a).
  apply lt_le_trans with (2^b); trivial.
  apply pow_pos_nonneg; order'.
 assert (Hc := log2_nonneg a).
 destruct (log2_spec a Ha) as (LEc,LTc).
 assert (log2 a <= b).
  apply lt_succ_r, (pow_lt_mono_r_iff 2); try order'.
  now apply le_le_succ_r.
 assert (b <= log2 a).
  apply lt_succ_r, (pow_lt_mono_r_iff 2); try order'.
  now apply le_le_succ_r.
 order.
Qed.

(** Hence log2 is a morphism. *)

Instance log2_wd : Proper (eq==>eq) log2.
Proof.
 intros x x' Hx.
 destruct (le_gt_cases x 0).
 rewrite 2 log2_nonpos; trivial. reflexivity. now rewrite <- Hx.
 apply log2_unique. apply log2_nonneg.
 rewrite Hx in *. now apply log2_spec.
Qed.

(** An alternate specification *)

Lemma log2_spec_alt : forall a, 0<a -> exists r,
 a == 2^(log2 a) + r /\ 0 <= r < 2^(log2 a).
Proof.
 intros a Ha.
 destruct (log2_spec _ Ha) as (LE,LT).
 destruct (le_exists_sub _ _ LE) as (r & Hr & Hr').
 exists r.
 split. now rewrite add_comm.
 split. trivial.
 apply (add_lt_mono_r _ _ (2^log2 a)).
 rewrite <- Hr. generalize LT.
 rewrite pow_succ_r by order_pos.
 rewrite two_succ at 1. now nzsimpl.
Qed.

Lemma log2_unique' : forall a b c, 0<=b -> 0<=c<2^b ->
 a == 2^b + c -> log2 a == b.
Proof.
 intros a b c Hb (Hc,H) EQ.
 apply log2_unique. trivial.
 rewrite EQ.
 split.
 rewrite <- add_0_r at 1. now apply add_le_mono_l.
 rewrite pow_succ_r by order.
 rewrite two_succ at 2. nzsimpl. now apply add_lt_mono_l.
Qed.

(** log2 is exact on powers of 2 *)

Lemma log2_pow2 : forall a, 0<=a -> log2 (2^a) == a.
Proof.
 intros a Ha.
 apply log2_unique' with 0; trivial.
 split; order_pos. now nzsimpl.
Qed.

(** log2 and basic constants *)

Lemma log2_1 : log2 1 == 0.
Proof.
 rewrite <- (pow_0_r 2). now apply log2_pow2.
Qed.

Lemma log2_2 : log2 2 == 1.
Proof.
 rewrite <- (pow_1_r 2). apply log2_pow2; order'.
Qed.

(** log2 n is strictly positive for 1<n *)

Lemma log2_pos : forall a, 1<a -> 0 < log2 a.
Proof.
 intros a Ha.
 assert (Ha' : 0 < a) by order'.
 assert (H := log2_nonneg a). apply le_lteq in H.
  destruct H; trivial.
 generalize (log2_spec a Ha'). rewrite <- H in *. nzsimpl; try order.
 intros (_,H'). rewrite two_succ in H'. apply lt_succ_r in H'; order.
Qed.

(** Said otherwise, log2 is null only below 1 *)

Lemma log2_null : forall a, log2 a == 0 <-> a <= 1.
Proof.
 intros a. split; intros H.
 destruct (le_gt_cases a 1) as [Ha|Ha]; trivial.
 generalize (log2_pos a Ha); order.
 apply le_lteq in H; destruct H.
 apply log2_nonpos. apply lt_succ_r. now rewrite <- one_succ.
 rewrite H. apply log2_1.
Qed.

(** log2 is a monotone function (but not a strict one) *)

Lemma log2_le_mono : forall a b, a<=b -> log2 a <= log2 b.
Proof.
 intros a b H.
 destruct (le_gt_cases a 0) as [Ha|Ha].
 rewrite log2_nonpos; order_pos.
 assert (Hb : 0 < b) by order.
 destruct (log2_spec a Ha) as (LEa,_).
 destruct (log2_spec b Hb) as (_,LTb).
 apply lt_succ_r, (pow_lt_mono_r_iff 2); order_pos.
Qed.

(** No reverse result for <=, consider for instance log2 3 <= log2 2 *)

Lemma log2_lt_cancel : forall a b, log2 a < log2 b -> a < b.
Proof.
 intros a b H.
 destruct (le_gt_cases b 0) as [Hb|Hb].
  rewrite (log2_nonpos b) in H; trivial.
  generalize (log2_nonneg a); order.
 destruct (le_gt_cases a 0) as [Ha|Ha]. order.
 destruct (log2_spec a Ha) as (_,LTa).
 destruct (log2_spec b Hb) as (LEb,_).
 apply le_succ_l in H.
 apply (pow_le_mono_r_iff 2) in H; order_pos.
Qed.

(** When left side is a power of 2, we have an equivalence for <= *)

Lemma log2_le_pow2 : forall a b, 0<a -> 0<=b -> (2^b<=a <-> b <= log2 a).
Proof.
 intros a b Ha Hb.
 split; intros H.
 rewrite <- (log2_pow2 b); trivial. now apply log2_le_mono.
 transitivity (2^(log2 a)).
 apply pow_le_mono_r; order'.
 now destruct (log2_spec a Ha).
Qed.

(** When right side is a square, we have an equivalence for < *)

Lemma log2_lt_pow2 : forall a b, 0<a -> 0<=b -> (a<2^b <-> log2 a < b).
Proof.
 intros a b Ha Hb.
 split; intros H.
 apply (pow_lt_mono_r_iff 2); try order_pos.
 apply le_lt_trans with a; trivial.
 now destruct (log2_spec a Ha).
 apply log2_lt_cancel; try order.
 now rewrite log2_pow2.
Qed.

(** Comparing log2 and identity *)

Lemma log2_lt_lin : forall a, 0<a -> log2 a < a.
Proof.
 intros a Ha.
 apply (pow_lt_mono_r_iff 2); try order_pos.
 apply le_lt_trans with a.
 now destruct (log2_spec a Ha).
 apply pow_gt_lin_r; order'.
Qed.

Lemma log2_le_lin : forall a, 0<=a -> log2 a <= a.
Proof.
 intros a Ha.
 apply le_lteq in Ha; destruct Ha as [Ha|Ha].
 now apply lt_le_incl, log2_lt_lin.
 rewrite <- Ha, log2_nonpos; order.
Qed.

(** Log2 and multiplication. *)

(** Due to rounding error, we don't have the usual
    [log2 (a*b) = log2 a + log2 b] but we may be off by 1 at most *)

Lemma log2_mul_below : forall a b, 0<a -> 0<b ->
 log2 a + log2 b <= log2 (a*b).
Proof.
 intros a b Ha Hb.
 apply log2_le_pow2; try order_pos.
 rewrite pow_add_r by order_pos.
 apply mul_le_mono_nonneg; try apply log2_spec; order_pos.
Qed.

Lemma log2_mul_above : forall a b, 0<=a -> 0<=b ->
 log2 (a*b) <= log2 a + log2 b + 1.
Proof.
 intros a b Ha Hb.
 apply le_lteq in Ha. destruct Ha as [Ha|Ha].
 apply le_lteq in Hb. destruct Hb as [Hb|Hb].
 apply lt_succ_r.
 rewrite add_1_r, <- add_succ_r, <- add_succ_l.
 apply log2_lt_pow2; try order_pos.
 rewrite pow_add_r by order_pos.
 apply mul_lt_mono_nonneg; try order; now apply log2_spec.
 rewrite <- Hb. nzsimpl. rewrite log2_nonpos; order_pos.
 rewrite <- Ha. nzsimpl. rewrite log2_nonpos; order_pos.
Qed.

(** And we can't find better approximations in general.
    - The lower bound is exact for powers of 2.
    - Concerning the upper bound, for any c>0, take a=b=2^c-1,
      then log2 (a*b) = c+c -1 while (log2 a) = (log2 b) = c-1
*)

(** Log2 and addition *)

Lemma log2_add_le : forall a b, a~=1 -> b~=1 -> log2 (a+b) <= log2 a + log2 b.
Proof.
 intros a b Ha Hb.
 destruct (lt_trichotomy a 1) as [Ha'|[Ha'|Ha']]; [|order|].
 rewrite one_succ, lt_succ_r in Ha'.
 rewrite (log2_nonpos a); trivial. nzsimpl. apply log2_le_mono.
 rewrite <- (add_0_l b) at 2. now apply add_le_mono.
 destruct (lt_trichotomy b 1) as [Hb'|[Hb'|Hb']]; [|order|].
 rewrite one_succ, lt_succ_r in Hb'.
 rewrite (log2_nonpos b); trivial. nzsimpl. apply log2_le_mono.
 rewrite <- (add_0_r a) at 2. now apply add_le_mono.
 clear Ha Hb.
 apply lt_succ_r.
 apply log2_lt_pow2; try order_pos.
 rewrite pow_succ_r by order_pos.
 rewrite two_succ, one_succ at 1. nzsimpl.
 apply add_lt_mono.
 apply lt_le_trans with (2^(S (log2 a))). apply log2_spec; order'.
 apply pow_le_mono_r. order'. rewrite <- add_1_r. apply add_le_mono_l.
  rewrite one_succ; now apply le_succ_l, log2_pos.
 apply lt_le_trans with (2^(S (log2 b))). apply log2_spec; order'.
 apply pow_le_mono_r. order'. rewrite <- add_1_l. apply add_le_mono_r.
  rewrite one_succ; now apply le_succ_l, log2_pos.
Qed.

(** The sum of two log2 is less than twice the log2 of the sum.
    This can almost be seen as a convexity inequality. *)

Lemma add_log2_lt : forall a b, 0<a -> 0<b ->
 log2 a + log2 b < 2 * log2 (a+b).
Proof.
 intros a b Ha Hb.
 apply (pow_lt_mono_r_iff 2); try order_pos.
 rewrite !pow_add_r by order_pos.
 apply le_lt_trans with (a*b).
  apply mul_le_mono_nonneg; try order_pos; now apply log2_spec.
 apply (mul_lt_mono_pos_r (2^2)).
 apply pow_pos_nonneg; order'.
 rewrite (mul_comm 2).
 rewrite <- pow_add_r by order_pos.
 rewrite <- mul_succ_l.
 rewrite pow_mul_r by order_pos.
 apply le_lt_trans with ((a+b)^2).
 rewrite !pow_2_r, (mul_comm (a*b)), mul_assoc.
 apply quadmul_le_squareadd; order.
 apply pow_lt_mono_l. order'. split. order_pos.
 apply log2_spec; order_pos.
Qed.

(** We can't be more precise : consider for instance a=2 b=4, then 1+2<2*2 *)

End NZLog2Prop.
