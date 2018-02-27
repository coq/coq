(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Base-2 Logarithm *)

Require Import NZAxioms NZMulOrder NZPow.

(** Interface of a log2 function, then its specification on naturals *)

Module Type Log2 (Import A : Typ).
 Parameter Inline log2 : t -> t.
End Log2.

Module Type NZLog2Spec (A : NZOrdAxiomsSig')(B : Pow' A)(C : Log2 A).
 Import A B C.
 Axiom log2_spec : forall a, 0<a -> 2^(log2 a) <= a < 2^(S (log2 a)).
 Axiom log2_nonpos : forall a, a<=0 -> log2 a == 0.
End NZLog2Spec.

Module Type NZLog2 (A : NZOrdAxiomsSig)(B : Pow A) := Log2 A <+ NZLog2Spec A B.

(** Derived properties of logarithm *)

Module Type NZLog2Prop
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

(** log2 and predecessors of powers of 2 *)

Lemma log2_pred_pow2 : forall a, 0<a -> log2 (P (2^a)) == P a.
Proof.
 intros a Ha.
 assert (Ha' : S (P a) == a) by (now rewrite lt_succ_pred with 0).
 apply log2_unique.
 apply lt_succ_r; order.
 rewrite <-le_succ_l, <-lt_succ_r, Ha'.
 rewrite lt_succ_pred with 0.
 split; try easy. apply pow_lt_mono_r_iff; try order'.
  rewrite succ_lt_mono, Ha'. apply lt_succ_diag_r.
 apply pow_pos_nonneg; order'.
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
 assert (H := log2_nonneg a). le_elim H; trivial.
 generalize (log2_spec a Ha'). rewrite <- H in *. nzsimpl; try order.
 intros (_,H'). rewrite two_succ in H'. apply lt_succ_r in H'; order.
Qed.

(** Said otherwise, log2 is null only below 1 *)

Lemma log2_null : forall a, log2 a == 0 <-> a <= 1.
Proof.
 intros a. split; intros H.
 destruct (le_gt_cases a 1) as [Ha|Ha]; trivial.
 generalize (log2_pos a Ha); order.
 le_elim H.
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

Lemma log2_le_pow2 : forall a b, 0<a -> (2^b<=a <-> b <= log2 a).
Proof.
 intros a b Ha.
 split; intros H.
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 generalize (log2_nonneg a); order.
 rewrite <- (log2_pow2 b); trivial. now apply log2_le_mono.
 transitivity (2^(log2 a)).
 apply pow_le_mono_r; order'.
 now destruct (log2_spec a Ha).
Qed.

(** When right side is a square, we have an equivalence for < *)

Lemma log2_lt_pow2 : forall a b, 0<a -> (a<2^b <-> log2 a < b).
Proof.
 intros a b Ha.
 split; intros H.
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 rewrite pow_neg_r in H; order.
 apply (pow_lt_mono_r_iff 2); try order_pos.
 apply le_lt_trans with a; trivial.
 now destruct (log2_spec a Ha).
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 generalize (log2_nonneg a); order.
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
 le_elim Ha.
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
 le_elim Ha.
 le_elim Hb.
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
    - Concerning the upper bound, for any c>1, take a=b=2^c-1,
      then log2 (a*b) = c+c -1 while (log2 a) = (log2 b) = c-1
*)

(** At least, we get back the usual equation when we multiply by 2 (or 2^k) *)

Lemma log2_mul_pow2 : forall a b, 0<a -> 0<=b -> log2 (a*2^b) == b + log2 a.
Proof.
 intros a b Ha Hb.
 apply log2_unique; try order_pos. split.
 rewrite pow_add_r, mul_comm; try order_pos.
 apply mul_le_mono_nonneg_r. order_pos. now apply log2_spec.
 rewrite <-add_succ_r, pow_add_r, mul_comm; try order_pos.
 apply mul_lt_mono_pos_l. order_pos. now apply log2_spec.
Qed.

Lemma log2_double : forall a, 0<a -> log2 (2*a) == S (log2 a).
Proof.
 intros a Ha. generalize (log2_mul_pow2 a 1 Ha le_0_1). now nzsimpl'.
Qed.

(** Two numbers with same log2 cannot be far away. *)

Lemma log2_same : forall a b, 0<a -> 0<b -> log2 a == log2 b -> a < 2*b.
Proof.
 intros a b Ha Hb H.
 apply log2_lt_cancel. rewrite log2_double, H by trivial.
 apply lt_succ_diag_r.
Qed.

(** Log2 and successor :
    - the log2 function climbs by at most 1 at a time
    - otherwise it stays at the same value
    - the +1 steps occur for powers of two
*)

Lemma log2_succ_le : forall a, log2 (S a) <= S (log2 a).
Proof.
 intros a.
 destruct (lt_trichotomy 0 a) as [LT|[EQ|LT]].
 apply (pow_le_mono_r_iff 2); try order_pos.
 transitivity (S a).
 apply log2_spec.
 apply lt_succ_r; order.
 now apply le_succ_l, log2_spec.
 rewrite <- EQ, <- one_succ, log2_1; order_pos.
 rewrite 2 log2_nonpos. order_pos. order'. now rewrite le_succ_l.
Qed.

Lemma log2_succ_or : forall a,
 log2 (S a) == S (log2 a) \/ log2 (S a) == log2 a.
Proof.
 intros.
 destruct (le_gt_cases (log2 (S a)) (log2 a)) as [H|H].
 right. generalize (log2_le_mono _ _ (le_succ_diag_r a)); order.
 left. apply le_succ_l in H. generalize (log2_succ_le a); order.
Qed.

Lemma log2_eq_succ_is_pow2 : forall a,
 log2 (S a) == S (log2 a) -> exists b, S a == 2^b.
Proof.
 intros a H.
 destruct (le_gt_cases a 0) as [Ha|Ha].
 rewrite 2 (proj2 (log2_null _)) in H. generalize (lt_succ_diag_r 0); order.
 order'. apply le_succ_l. order'.
 assert (Ha' : 0 < S a) by (apply lt_succ_r; order).
 exists (log2 (S a)).
 generalize (proj1 (log2_spec (S a) Ha')) (proj2 (log2_spec a Ha)).
 rewrite <- le_succ_l, <- H. order.
Qed.

Lemma log2_eq_succ_iff_pow2 : forall a, 0<a ->
 (log2 (S a) == S (log2 a) <-> exists b, S a == 2^b).
Proof.
 intros a Ha.
 split. apply log2_eq_succ_is_pow2.
 intros (b,Hb).
 assert (Hb' : 0 < b).
  apply (pow_gt_1 2); try order'; now rewrite <- Hb, one_succ, <- succ_lt_mono.
 rewrite Hb, log2_pow2; try order'.
 setoid_replace a with (P (2^b)). rewrite log2_pred_pow2; trivial.
 symmetry; now apply lt_succ_pred with 0.
 apply succ_inj. rewrite Hb. symmetry. apply lt_succ_pred with 0.
  rewrite <- Hb, lt_succ_r; order.
Qed.

Lemma log2_succ_double : forall a, 0<a -> log2 (2*a+1) == S (log2 a).
Proof.
 intros a Ha.
 rewrite add_1_r.
 destruct (log2_succ_or (2*a)) as [H|H]; [exfalso|now rewrite H, log2_double].
 apply log2_eq_succ_is_pow2 in H. destruct H as (b,H).
 destruct (lt_trichotomy b 0) as [LT|[EQ|LT]].
 rewrite pow_neg_r in H; trivial.
 apply (mul_pos_pos 2), succ_lt_mono in Ha; try order'.
 rewrite <- one_succ in Ha. order'.
 rewrite EQ, pow_0_r in H.
 apply (mul_pos_pos 2), succ_lt_mono in Ha; try order'.
 rewrite <- one_succ in Ha. order'.
 assert (EQ:=lt_succ_pred 0 b LT).
 rewrite <- EQ, pow_succ_r in H; [|now rewrite <- lt_succ_r, EQ].
 destruct (lt_ge_cases a (2^(P b))) as [LT'|LE'].
 generalize (mul_2_mono_l _ _ LT'). rewrite add_1_l. order.
 rewrite (mul_le_mono_pos_l _ _ 2) in LE'; try order'.
 rewrite <- H in LE'. apply le_succ_l in LE'. order.
Qed.

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
    The large inequality is obvious thanks to monotonicity.
    The strict one requires some more work. This is almost
    a convexity inequality for points [2a], [2b] and their middle [a+b] :
    ideally, we would have [2*log(a+b) >= log(2a)+log(2b) = 2+log a+log b].
    Here, we cannot do better: consider for instance a=2 b=4, then 1+2<2*2
*)

Lemma add_log2_lt : forall a b, 0<a -> 0<b ->
 log2 a + log2 b < 2 * log2 (a+b).
Proof.
 intros a b Ha Hb. nzsimpl'.
 assert (H : log2 a <= log2 (a+b)).
  apply log2_le_mono. rewrite <- (add_0_r a) at 1. apply add_le_mono; order.
 assert (H' : log2 b <= log2 (a+b)).
  apply log2_le_mono. rewrite <- (add_0_l b) at 1. apply add_le_mono; order.
 le_elim H.
 apply lt_le_trans with (log2 (a+b) + log2 b).
  now apply add_lt_mono_r. now apply add_le_mono_l.
 rewrite <- H at 1. apply add_lt_mono_l.
 le_elim H'; trivial.
 symmetry in H. apply log2_same in H; try order_pos.
 symmetry in H'. apply log2_same in H'; try order_pos.
 revert H H'. nzsimpl'. rewrite <- add_lt_mono_l, <- add_lt_mono_r; order.
Qed.

End NZLog2Prop.

Module NZLog2UpProp
 (Import A : NZDecOrdAxiomsSig')
 (Import B : NZPow' A)
 (Import C : NZLog2 A B)
 (Import D : NZMulOrderProp A)
 (Import E : NZPowProp A B D)
 (Import F : NZLog2Prop A B C D E).

(** * [log2_up] : a binary logarithm that rounds up instead of down *)

(** For once, we define instead of axiomatizing, thanks to log2 *)

Definition log2_up a :=
 match compare 1 a with
  | Lt => S (log2 (P a))
  | _ => 0
 end.

Lemma log2_up_eqn0 : forall a, a<=1 -> log2_up a == 0.
Proof.
 intros a Ha. unfold log2_up. case compare_spec; try order.
Qed.

Lemma log2_up_eqn : forall a, 1<a -> log2_up a == S (log2 (P a)).
Proof.
 intros a Ha. unfold log2_up. case compare_spec; try order.
Qed.

Lemma log2_up_spec : forall a, 1<a ->
 2^(P (log2_up a)) < a <= 2^(log2_up a).
Proof.
 intros a Ha.
 rewrite log2_up_eqn; trivial.
 rewrite pred_succ.
 rewrite <- (lt_succ_pred 1 a Ha) at 2 3.
 rewrite lt_succ_r, le_succ_l.
 apply log2_spec.
 apply succ_lt_mono. now rewrite (lt_succ_pred 1 a Ha), <- one_succ.
Qed.

Lemma log2_up_nonpos : forall a, a<=0 -> log2_up a == 0.
Proof.
 intros. apply log2_up_eqn0. order'.
Qed.

Instance log2_up_wd : Proper (eq==>eq) log2_up.
Proof.
 assert (Proper (eq==>eq==>Logic.eq) compare).
  repeat red; intros; do 2 case compare_spec; trivial; order.
 intros a a' Ha. unfold log2_up. rewrite Ha at 1.
 case compare; now rewrite ?Ha.
Qed.

(** [log2_up] is always non-negative *)

Lemma log2_up_nonneg : forall a, 0 <= log2_up a.
Proof.
 intros a. unfold log2_up. case compare_spec; try order.
 intros. apply le_le_succ_r, log2_nonneg.
Qed.

(** The spec of [log2_up] indeed determines it *)

Lemma log2_up_unique : forall a b, 0<b -> 2^(P b)<a<=2^b -> log2_up a == b.
Proof.
 intros a b Hb (LEb,LTb).
 assert (Ha : 1 < a).
  apply le_lt_trans with (2^(P b)); trivial.
  rewrite one_succ. apply le_succ_l.
  apply pow_pos_nonneg. order'. apply lt_succ_r.
  now rewrite (lt_succ_pred 0 b Hb).
 assert (Hc := log2_up_nonneg a).
 destruct (log2_up_spec a Ha) as (LTc,LEc).
 assert (b <= log2_up a).
  apply lt_succ_r. rewrite <- (lt_succ_pred 0 b Hb).
  rewrite <- succ_lt_mono.
  apply (pow_lt_mono_r_iff 2); try order'.
 assert (Hc' : 0 < log2_up a) by order.
 assert (log2_up a <= b).
  apply lt_succ_r. rewrite <- (lt_succ_pred 0 _ Hc').
  rewrite <- succ_lt_mono.
  apply (pow_lt_mono_r_iff 2); try order'.
 order.
Qed.

(** [log2_up] is exact on powers of 2 *)

Lemma log2_up_pow2 : forall a, 0<=a -> log2_up (2^a) == a.
Proof.
 intros a Ha.
 le_elim Ha.
 apply log2_up_unique; trivial.
 split; try order.
 apply pow_lt_mono_r; try order'.
 rewrite <- (lt_succ_pred 0 a Ha) at 2.
 now apply lt_succ_r.
 now rewrite <- Ha, pow_0_r, log2_up_eqn0.
Qed.

(** [log2_up] and successors of powers of 2 *)

Lemma log2_up_succ_pow2 : forall a, 0<=a -> log2_up (S (2^a)) == S a.
Proof.
 intros a Ha.
 rewrite log2_up_eqn, pred_succ, log2_pow2; try easy.
 rewrite one_succ, <- succ_lt_mono. apply pow_pos_nonneg; order'.
Qed.

(** Basic constants *)

Lemma log2_up_1 : log2_up 1 == 0.
Proof.
 now apply log2_up_eqn0.
Qed.

Lemma log2_up_2 : log2_up 2 == 1.
Proof.
 rewrite <- (pow_1_r 2). apply log2_up_pow2; order'.
Qed.

(** Links between log2 and [log2_up] *)

Lemma le_log2_log2_up : forall a, log2 a <= log2_up a.
Proof.
 intros a. unfold log2_up. case compare_spec; intros H.
 rewrite <- H, log2_1. order.
 rewrite <- (lt_succ_pred 1 a H) at 1. apply log2_succ_le.
 rewrite log2_nonpos. order. now rewrite <-lt_succ_r, <-one_succ.
Qed.

Lemma le_log2_up_succ_log2 : forall a, log2_up a <= S (log2 a).
Proof.
 intros a. unfold log2_up. case compare_spec; intros H; try order_pos.
 rewrite <- succ_le_mono. apply log2_le_mono.
 rewrite <- (lt_succ_pred 1 a H) at 2. apply le_succ_diag_r.
Qed.

Lemma log2_log2_up_spec : forall a, 0<a ->
 2^log2 a <= a <= 2^log2_up a.
Proof.
 intros a H. split.
 now apply log2_spec.
 rewrite <-le_succ_l, <-one_succ in H. le_elim H.
 now apply log2_up_spec.
 now rewrite <-H, log2_up_1, pow_0_r.
Qed.

Lemma log2_log2_up_exact :
 forall a, 0<a -> (log2 a == log2_up a <-> exists b, a == 2^b).
Proof.
 intros a Ha.
 split. intros. exists (log2 a).
  generalize (log2_log2_up_spec a Ha). rewrite <-H.
  destruct 1; order.
 intros (b,Hb). rewrite Hb.
 destruct (le_gt_cases 0 b).
 now rewrite log2_pow2, log2_up_pow2.
 rewrite pow_neg_r; trivial. now rewrite log2_nonpos, log2_up_nonpos.
Qed.

(** [log2_up] n is strictly positive for 1<n *)

Lemma log2_up_pos : forall a, 1<a -> 0 < log2_up a.
Proof.
 intros. rewrite log2_up_eqn; trivial. apply lt_succ_r; order_pos.
Qed.

(** Said otherwise, [log2_up] is null only below 1 *)

Lemma log2_up_null : forall a, log2_up a == 0 <-> a <= 1.
Proof.
 intros a. split; intros H.
 destruct (le_gt_cases a 1) as [Ha|Ha]; trivial.
 generalize (log2_up_pos a Ha); order.
 now apply log2_up_eqn0.
Qed.

(** [log2_up] is a monotone function (but not a strict one) *)

Lemma log2_up_le_mono : forall a b, a<=b -> log2_up a <= log2_up b.
Proof.
 intros a b H.
 destruct (le_gt_cases a 1) as [Ha|Ha].
 rewrite log2_up_eqn0; trivial. apply log2_up_nonneg.
 rewrite 2 log2_up_eqn; try order.
 rewrite <- succ_le_mono. apply log2_le_mono, succ_le_mono.
 rewrite 2 lt_succ_pred with 1; order.
Qed.

(** No reverse result for <=, consider for instance log2_up 4 <= log2_up 3 *)

Lemma log2_up_lt_cancel : forall a b, log2_up a < log2_up b -> a < b.
Proof.
 intros a b H.
 destruct (le_gt_cases b 1) as [Hb|Hb].
  rewrite (log2_up_eqn0 b) in H; trivial.
  generalize (log2_up_nonneg a); order.
 destruct (le_gt_cases a 1) as [Ha|Ha]. order.
 rewrite 2 log2_up_eqn in H; try order.
 rewrite <- succ_lt_mono in H. apply log2_lt_cancel, succ_lt_mono in H.
 rewrite 2 lt_succ_pred with 1 in H; order.
Qed.

(** When left side is a power of 2, we have an equivalence for < *)

Lemma log2_up_lt_pow2 : forall a b, 0<a -> (2^b<a <-> b < log2_up a).
Proof.
 intros a b Ha.
 split; intros H.
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 generalize (log2_up_nonneg a); order.
 apply (pow_lt_mono_r_iff 2). order'. apply log2_up_nonneg.
 apply lt_le_trans with a; trivial.
 apply (log2_up_spec a).
 apply le_lt_trans with (2^b); trivial.
 rewrite one_succ, le_succ_l. apply pow_pos_nonneg; order'.
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 now rewrite pow_neg_r.
 rewrite <- (log2_up_pow2 b) in H; trivial. now apply log2_up_lt_cancel.
Qed.

(** When right side is a square, we have an equivalence for <= *)

Lemma log2_up_le_pow2 : forall a b, 0<a -> (a<=2^b <-> log2_up a <= b).
Proof.
 intros a b Ha.
 split; intros H.
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 rewrite pow_neg_r in H; order.
 rewrite <- (log2_up_pow2 b); trivial. now apply log2_up_le_mono.
 transitivity (2^(log2_up a)).
 now apply log2_log2_up_spec.
 apply pow_le_mono_r; order'.
Qed.

(** Comparing [log2_up] and identity *)

Lemma log2_up_lt_lin : forall a, 0<a -> log2_up a < a.
Proof.
 intros a Ha.
 assert (H : S (P a) == a) by (now apply lt_succ_pred with 0).
 rewrite <- H at 2. apply lt_succ_r. apply log2_up_le_pow2; trivial.
 rewrite <- H at 1. apply le_succ_l.
 apply pow_gt_lin_r. order'. apply lt_succ_r; order.
Qed.

Lemma log2_up_le_lin : forall a, 0<=a -> log2_up a <= a.
Proof.
 intros a Ha.
 le_elim Ha.
 now apply lt_le_incl, log2_up_lt_lin.
 rewrite <- Ha, log2_up_nonpos; order.
Qed.

(** [log2_up] and multiplication. *)

(** Due to rounding error, we don't have the usual
    [log2_up (a*b) = log2_up a + log2_up b] but we may be off by 1 at most *)

Lemma log2_up_mul_above : forall a b, 0<=a -> 0<=b ->
  log2_up (a*b) <= log2_up a + log2_up b.
Proof.
 intros a b Ha Hb.
 assert (Ha':=log2_up_nonneg a).
 assert (Hb':=log2_up_nonneg b).
 le_elim Ha.
 le_elim Hb.
 apply log2_up_le_pow2; try order_pos.
 rewrite pow_add_r; trivial.
 apply mul_le_mono_nonneg; try apply log2_log2_up_spec; order'.
 rewrite <- Hb. nzsimpl. rewrite log2_up_nonpos; order_pos.
 rewrite <- Ha. nzsimpl. rewrite log2_up_nonpos; order_pos.
Qed.

Lemma log2_up_mul_below : forall a b, 0<a -> 0<b ->
 log2_up a + log2_up b <= S (log2_up (a*b)).
Proof.
 intros a b Ha Hb.
 rewrite <-le_succ_l, <-one_succ in Ha. le_elim Ha.
 rewrite <-le_succ_l, <-one_succ in Hb. le_elim Hb.
 assert (Ha' : 0 < log2_up a) by (apply log2_up_pos; trivial).
 assert (Hb' : 0 < log2_up b) by (apply log2_up_pos; trivial).
 rewrite <- (lt_succ_pred 0 (log2_up a)); trivial.
 rewrite <- (lt_succ_pred 0 (log2_up b)); trivial.
 nzsimpl. rewrite <- succ_le_mono, le_succ_l.
 apply (pow_lt_mono_r_iff 2). order'. apply log2_up_nonneg.
 rewrite pow_add_r; try (apply lt_succ_r; rewrite (lt_succ_pred 0); trivial).
 apply lt_le_trans with (a*b).
 apply mul_lt_mono_nonneg; try order_pos; try now apply log2_up_spec.
 apply log2_up_spec.
 setoid_replace 1 with (1*1) by now nzsimpl.
 apply mul_lt_mono_nonneg; order'.
 rewrite <- Hb, log2_up_1; nzsimpl. apply le_succ_diag_r.
 rewrite <- Ha, log2_up_1; nzsimpl. apply le_succ_diag_r.
Qed.

(** And we can't find better approximations in general.
    - The upper bound is exact for powers of 2.
    - Concerning the lower bound, for any c>1, take a=b=2^c+1,
      then [log2_up (a*b) = c+c +1] while [(log2_up a) = (log2_up b) = c+1]
*)

(** At least, we get back the usual equation when we multiply by 2 (or 2^k) *)

Lemma log2_up_mul_pow2 : forall a b, 0<a -> 0<=b ->
 log2_up (a*2^b) == b + log2_up a.
Proof.
 intros a b Ha Hb.
 rewrite <- le_succ_l, <- one_succ in Ha; le_elim Ha.
 apply log2_up_unique. apply add_nonneg_pos; trivial. now apply log2_up_pos.
 split.
 assert (EQ := lt_succ_pred 0 _ (log2_up_pos _ Ha)).
 rewrite <- EQ. nzsimpl. rewrite pow_add_r, mul_comm; trivial.
 apply mul_lt_mono_pos_r. order_pos. now apply log2_up_spec.
 rewrite <- lt_succ_r, EQ. now apply log2_up_pos.
 rewrite pow_add_r, mul_comm; trivial.
 apply mul_le_mono_nonneg_l. order_pos. now apply log2_up_spec.
 apply log2_up_nonneg.
 now rewrite <- Ha, mul_1_l, log2_up_1, add_0_r, log2_up_pow2.
Qed.

Lemma log2_up_double : forall a, 0<a -> log2_up (2*a) == S (log2_up a).
Proof.
 intros a Ha. generalize (log2_up_mul_pow2 a 1 Ha le_0_1). now nzsimpl'.
Qed.

(** Two numbers with same [log2_up] cannot be far away. *)

Lemma log2_up_same : forall a b, 0<a -> 0<b -> log2_up a == log2_up b -> a < 2*b.
Proof.
 intros a b Ha Hb H.
 apply log2_up_lt_cancel. rewrite log2_up_double, H by trivial.
 apply lt_succ_diag_r.
Qed.

(** [log2_up] and successor :
    - the [log2_up] function climbs by at most 1 at a time
    - otherwise it stays at the same value
    - the +1 steps occur after powers of two
*)

Lemma log2_up_succ_le : forall a, log2_up (S a) <= S (log2_up a).
Proof.
 intros a.
 destruct (lt_trichotomy 1 a) as [LT|[EQ|LT]].
 rewrite 2 log2_up_eqn; trivial.
 rewrite pred_succ, <- succ_le_mono. rewrite <-(lt_succ_pred 1 a LT) at 1.
 apply log2_succ_le.
 apply lt_succ_r; order.
 rewrite <- EQ, <- two_succ, log2_up_1, log2_up_2. now nzsimpl'.
 rewrite 2 log2_up_eqn0. order_pos. order'. now rewrite le_succ_l.
Qed.

Lemma log2_up_succ_or : forall a,
 log2_up (S a) == S (log2_up a) \/ log2_up (S a) == log2_up a.
Proof.
 intros.
 destruct (le_gt_cases (log2_up (S a)) (log2_up a)).
 right. generalize (log2_up_le_mono _ _ (le_succ_diag_r a)); order.
 left. apply le_succ_l in H. generalize (log2_up_succ_le a); order.
Qed.

Lemma log2_up_eq_succ_is_pow2 : forall a,
 log2_up (S a) == S (log2_up a) -> exists b, a == 2^b.
Proof.
 intros a H.
 destruct (le_gt_cases a 0) as [Ha|Ha].
 rewrite 2 (proj2 (log2_up_null _)) in H. generalize (lt_succ_diag_r 0); order.
 order'. apply le_succ_l. order'.
 assert (Ha' : 1 < S a) by (now rewrite one_succ, <- succ_lt_mono).
 exists (log2_up a).
 generalize (proj1 (log2_up_spec (S a) Ha')) (proj2 (log2_log2_up_spec a Ha)).
 rewrite H, pred_succ, lt_succ_r. order.
Qed.

Lemma log2_up_eq_succ_iff_pow2 : forall a, 0<a ->
 (log2_up (S a) == S (log2_up a) <-> exists b, a == 2^b).
Proof.
 intros a Ha.
 split. apply log2_up_eq_succ_is_pow2.
 intros (b,Hb).
 destruct (lt_ge_cases b 0) as [Hb'|Hb'].
  rewrite pow_neg_r in Hb; order.
 rewrite Hb, log2_up_pow2; try order'.
 now rewrite log2_up_succ_pow2.
Qed.

Lemma log2_up_succ_double : forall a, 0<a ->
 log2_up (2*a+1) == 2 + log2 a.
Proof.
 intros a Ha.
 rewrite log2_up_eqn. rewrite add_1_r, pred_succ, log2_double; now nzsimpl'.
 apply le_lt_trans with (0+1). now nzsimpl'.
 apply add_lt_mono_r. order_pos.
Qed.

(** [log2_up] and addition *)

Lemma log2_up_add_le : forall a b, a~=1 -> b~=1 ->
 log2_up (a+b) <= log2_up a + log2_up b.
Proof.
 intros a b Ha Hb.
 destruct (lt_trichotomy a 1) as [Ha'|[Ha'|Ha']]; [|order|].
 rewrite (log2_up_eqn0 a) by order. nzsimpl. apply log2_up_le_mono.
 rewrite one_succ, lt_succ_r in Ha'.
 rewrite <- (add_0_l b) at 2. now apply add_le_mono.
 destruct (lt_trichotomy b 1) as [Hb'|[Hb'|Hb']]; [|order|].
 rewrite (log2_up_eqn0 b) by order. nzsimpl. apply log2_up_le_mono.
 rewrite one_succ, lt_succ_r in Hb'.
 rewrite <- (add_0_r a) at 2. now apply add_le_mono.
 clear Ha Hb.
 transitivity (log2_up (a*b)).
 now apply log2_up_le_mono, add_le_mul.
 apply log2_up_mul_above; order'.
Qed.

(** The sum of two [log2_up] is less than twice the [log2_up] of the sum.
    The large inequality is obvious thanks to monotonicity.
    The strict one requires some more work. This is almost
    a convexity inequality for points [2a], [2b] and their middle [a+b] :
    ideally, we would have [2*log(a+b) >= log(2a)+log(2b) = 2+log a+log b].
    Here, we cannot do better: consider for instance a=3 b=5, then 2+3<2*3
*)

Lemma add_log2_up_lt : forall a b, 0<a -> 0<b ->
 log2_up a + log2_up b < 2 * log2_up (a+b).
Proof.
 intros a b Ha Hb. nzsimpl'.
 assert (H : log2_up a <= log2_up (a+b)).
  apply log2_up_le_mono. rewrite <- (add_0_r a) at 1. apply add_le_mono; order.
 assert (H' : log2_up b <= log2_up (a+b)).
  apply log2_up_le_mono. rewrite <- (add_0_l b) at 1. apply add_le_mono; order.
 le_elim H.
 apply lt_le_trans with (log2_up (a+b) + log2_up b).
  now apply add_lt_mono_r. now apply add_le_mono_l.
 rewrite <- H at 1. apply add_lt_mono_l.
 le_elim H'. trivial.
 symmetry in H. apply log2_up_same in H; try order_pos.
 symmetry in H'. apply log2_up_same in H'; try order_pos.
 revert H H'. nzsimpl'. rewrite <- add_lt_mono_l, <- add_lt_mono_r; order.
Qed.

End NZLog2UpProp.

