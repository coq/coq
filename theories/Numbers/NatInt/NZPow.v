(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Power Function *)

Require Import NZAxioms NZMulOrder.

(** Interface of a power function, then its specification on naturals *)

Module Type Pow (Import T:Typ).
 Parameters Inline pow : t -> t -> t.
End Pow.

Module Type PowNotation (T:Typ)(Import NZ:Pow T).
 Infix "^" := pow.
End PowNotation.

Module Type Pow' (T:Typ) := Pow T <+ PowNotation T.

Module Type NZPowSpec (Import NZ : NZOrdAxiomsSig')(Import P : Pow' NZ).
 Declare Instance pow_wd : Proper (eq==>eq==>eq) pow.
 Axiom pow_0_r : forall a, a^0 == 1.
 Axiom pow_succ_r : forall a b, 0<=b -> a^(succ b) == a * a^b.
End NZPowSpec.

Module Type NZPow (NZ:NZOrdAxiomsSig) := Pow NZ <+ NZPowSpec NZ.
Module Type NZPow' (NZ:NZOrdAxiomsSig) := Pow' NZ <+ NZPowSpec NZ.

(** Derived properties of power *)

Module NZPowProp
 (Import NZ : NZOrdAxiomsSig')
 (Import NZP : NZMulOrderProp NZ)
 (Import NZP' : NZPow' NZ).

Hint Rewrite pow_0_r pow_succ_r : nz.

Lemma lt_0_2 : 0 < 2.
Proof.
 apply lt_succ_r, le_0_1.
Qed.

Ltac order' := generalize lt_0_1 lt_0_2; order.

(** Power and basic constants *)

Lemma pow_0_l : forall a, 0<a -> 0^a == 0.
Proof.
 intros a Ha.
 destruct (lt_exists_pred _ _ Ha) as (a' & EQ & Ha').
 rewrite EQ. now nzsimpl.
Qed.

Lemma pow_1_r : forall a, a^1 == a.
Proof.
 intros. now nzsimpl.
Qed.

Lemma pow_1_l : forall a, 0<=a -> 1^a == 1.
Proof.
 apply le_ind; intros. solve_predicate_wd.
 now nzsimpl.
 now nzsimpl.
Qed.

Hint Rewrite pow_1_l : nz.

Lemma pow_2_r : forall a, a^2 == a*a.
Proof.
 intros. nzsimpl; order'.
Qed.

(** Power and addition, multiplication *)

Lemma pow_add_r : forall a b c, 0<=b -> 0<=c ->
  a^(b+c) == a^b * a^c.
Proof.
 intros a b c Hb. apply le_ind with (4:=Hb). solve_predicate_wd.
 now nzsimpl.
 clear b Hb. intros b Hb IH Hc.
 nzsimpl; trivial.
 rewrite IH; trivial. apply mul_assoc.
 now apply add_nonneg_nonneg.
Qed.

Lemma pow_mul_l : forall a b c, 0<=c ->
  (a*b)^c == a^c * b^c.
Proof.
 intros a b c Hc. apply le_ind with (4:=Hc). solve_predicate_wd.
 now nzsimpl.
 clear c Hc. intros c Hc IH.
 nzsimpl; trivial.
 rewrite IH; trivial. apply mul_shuffle1.
Qed.

Lemma pow_mul_r : forall a b c, 0<=b -> 0<=c ->
  a^(b*c) == (a^b)^c.
Proof.
 intros a b c Hb. apply le_ind with (4:=Hb). solve_predicate_wd.
 intros. now nzsimpl.
 clear b Hb. intros b Hb IH Hc.
 nzsimpl; trivial.
 rewrite pow_add_r, IH, pow_mul_l; trivial. apply mul_comm.
 now apply mul_nonneg_nonneg.
Qed.

(** Positivity *)

Lemma pow_nonneg_nonneg : forall a b, 0<=a -> 0<=b -> 0<=a^b.
Proof.
 intros a b Ha Hb. apply le_ind with (4:=Hb). solve_predicate_wd.
 nzsimpl; order'.
 clear b Hb. intros b Hb IH.
 nzsimpl; trivial. now apply mul_nonneg_nonneg.
Qed.

Lemma pow_pos_nonneg : forall a b, 0<a -> 0<=b -> 0<a^b.
Proof.
 intros a b Ha Hb. apply le_ind with (4:=Hb). solve_predicate_wd.
 nzsimpl; order'.
 clear b Hb. intros b Hb IH.
 nzsimpl; trivial. now apply mul_pos_pos.
Qed.

(** Monotonicity *)

Lemma pow_lt_mono_l : forall a b c, 0<c -> 0<=a<b -> a^c < b^c.
Proof.
 intros a b c Hc. apply lt_ind with (4:=Hc). solve_predicate_wd.
 intros (Ha,H). nzsimpl; trivial; order.
 clear c Hc. intros c Hc IH (Ha,H).
 nzsimpl; try order.
 apply mul_lt_mono_nonneg; trivial.
 apply pow_nonneg_nonneg; try order.
 apply IH. now split.
Qed.

Lemma pow_le_mono_l : forall a b c, 0<=c -> 0<=a<=b -> a^c <= b^c.
Proof.
 intros a b c Hc (Ha,H).
 apply lt_eq_cases in Hc; destruct Hc as [Hc|Hc]; [|rewrite <- Hc].
 apply lt_eq_cases in H. destruct H as [H|H]; [|now rewrite <- H].
 apply lt_le_incl, pow_lt_mono_l; now try split.
 now nzsimpl.
Qed.

Lemma pow_gt_1 : forall a b, 1<a -> 0<b -> 1<a^b.
Proof.
 intros a b Ha Hb. rewrite <- (pow_1_l b) by order.
 apply pow_lt_mono_l; try split; order'.
Qed.

Lemma pow_lt_mono_r : forall a b c, 1<a -> 0<=b<c -> a^b < a^c.
Proof.
 intros a b c Ha (Hb,H).
 assert (H' : b<=c) by order.
 destruct (le_exists_sub _ _ H') as (d & EQ & Hd).
 rewrite EQ, pow_add_r; trivial. rewrite <- (mul_1_l (a^b)) at 1.
 apply mul_lt_mono_pos_r.
 apply pow_pos_nonneg; order'.
 apply pow_gt_1; trivial.
 apply lt_eq_cases in Hd; destruct Hd as [LT|EQ']; trivial.
  rewrite <- EQ' in *. rewrite add_0_l in EQ. order.
Qed.

(** NB: since 0^0 > 0^1, the following result isn't valid with a=0 *)

Lemma pow_le_mono_r : forall a b c, 0<a -> 0<=b<=c -> a^b <= a^c.
Proof.
 intros a b c Ha (Hb,H).
 apply le_succ_l in Ha.
 apply lt_eq_cases in Ha; destruct Ha as [Ha|Ha]; [|rewrite <- Ha].
 apply lt_eq_cases in H; destruct H as [H|H]; [|now rewrite <- H].
 apply lt_le_incl, pow_lt_mono_r; now try split.
 nzsimpl; order.
Qed.

Lemma pow_le_mono : forall a b c d, 0<a<=c -> 0<=b<=d ->
 a^b <= c^d.
Proof.
 intros. transitivity (a^d).
 apply pow_le_mono_r; intuition order.
 apply pow_le_mono_l; intuition order.
Qed.

Lemma pow_lt_mono : forall a b c d, 0<a<c -> 0<b<d ->
 a^b < c^d.
Proof.
 intros a b c d (Ha,Hac) (Hb,Hbd).
 apply le_succ_l in Ha.
 apply lt_eq_cases in Ha; destruct Ha as [Ha|Ha]; [|rewrite <- Ha].
 transitivity (a^d).
 apply pow_lt_mono_r; intuition order.
 apply pow_lt_mono_l; try split; order'.
 nzsimpl; try order. apply pow_gt_1; order.
Qed.

(** Injectivity *)

Lemma pow_inj_l : forall a b c, 0<=a -> 0<=b -> 0<c ->
 a^c == b^c -> a == b.
Proof.
 intros a b c Ha Hb Hc EQ.
 destruct (lt_trichotomy a b) as [LT|[EQ'|GT]]; trivial.
 assert (a^c < b^c) by (apply pow_lt_mono_l; try split; trivial).
 order.
 assert (b^c < a^c) by (apply pow_lt_mono_l; try split; trivial).
 order.
Qed.

Lemma pow_inj_r : forall a b c, 1<a -> 0<=b -> 0<=c ->
 a^b == a^c -> b == c.
Proof.
 intros a b c Ha Hb Hc EQ.
 destruct (lt_trichotomy b c) as [LT|[EQ'|GT]]; trivial.
 assert (a^b < a^c) by (apply pow_lt_mono_r; try split; trivial).
 order.
 assert (a^c < a^b) by (apply pow_lt_mono_r; try split; trivial).
 order.
Qed.

(** Monotonicity results, both ways *)

Lemma pow_lt_mono_l_iff : forall a b c, 0<=a -> 0<=b -> 0<c ->
  (a<b <-> a^c < b^c).
Proof.
 intros a b c Ha Hb Hc.
 split; intro LT.
 apply pow_lt_mono_l; try split; trivial.
 destruct (le_gt_cases b a) as [LE|GT]; trivial.
 assert (b^c <= a^c) by (apply pow_le_mono_l; try split; order).
 order.
Qed.

Lemma pow_le_mono_l_iff : forall a b c, 0<=a -> 0<=b -> 0<c ->
  (a<=b <-> a^c <= b^c).
Proof.
 intros a b c Ha Hb Hc.
 split; intro LE.
 apply pow_le_mono_l; try split; trivial. order.
 destruct (le_gt_cases a b) as [LE'|GT]; trivial.
 assert (b^c < a^c) by (apply pow_lt_mono_l; try split; trivial).
 order.
Qed.

Lemma pow_lt_mono_r_iff : forall a b c, 1<a -> 0<=b -> 0<=c ->
  (b<c <-> a^b < a^c).
Proof.
 intros a b c Ha Hb Hc.
 split; intro LT.
 apply pow_lt_mono_r; try split; trivial.
 destruct (le_gt_cases c b) as [LE|GT]; trivial.
 assert (a^c <= a^b) by (apply pow_le_mono_r; try split; order').
 order.
Qed.

Lemma pow_le_mono_r_iff : forall a b c, 1<a -> 0<=b -> 0<=c ->
  (b<=c <-> a^b <= a^c).
Proof.
 intros a b c Ha Hb Hc.
 split; intro LE.
 apply pow_le_mono_r; try split; trivial. order'.
 destruct (le_gt_cases b c) as [LE'|GT]; trivial.
 assert (a^c < a^b) by (apply pow_lt_mono_r; try split; order').
 order.
Qed.

(** For any a>1, the a^x function is above the identity function *)

Lemma pow_gt_lin_r : forall a b, 1<a -> 0<=b -> b < a^b.
Proof.
 intros a b Ha Hb. apply le_ind with (4:=Hb). solve_predicate_wd.
 nzsimpl. order'.
 clear b Hb. intros b Hb IH. nzsimpl; trivial.
 rewrite <- !le_succ_l in *.
 transitivity (2*(S b)).
  nzsimpl. rewrite <- 2 succ_le_mono.
  rewrite <- (add_0_l b) at 1. apply add_le_mono; order.
 apply mul_le_mono_nonneg; trivial.
 order'.
 now apply lt_le_incl, lt_succ_r.
Qed.

(** Someday, we should say something about the full Newton formula.
    In the meantime, we can at least provide some inequalities about
    (a+b)^c.
*)

Lemma pow_add_lower : forall a b c, 0<=a -> 0<=b -> 0<c ->
  a^c + b^c <= (a+b)^c.
Proof.
 intros a b c Ha Hb Hc. apply lt_ind with (4:=Hc). solve_predicate_wd.
 nzsimpl; order.
 clear c Hc. intros c Hc IH.
 assert (0<=c) by order'.
 nzsimpl; trivial.
 transitivity ((a+b)*(a^c + b^c)).
 rewrite mul_add_distr_r, !mul_add_distr_l.
 apply add_le_mono.
 rewrite <- add_0_r at 1. apply add_le_mono_l.
  apply mul_nonneg_nonneg; trivial.
  apply pow_nonneg_nonneg; trivial.
 rewrite <- add_0_l at 1. apply add_le_mono_r.
  apply mul_nonneg_nonneg; trivial.
  apply pow_nonneg_nonneg; trivial.
 apply mul_le_mono_nonneg_l; trivial.
 now apply add_nonneg_nonneg.
Qed.

(** This upper bound can also be seen as a convexity proof for x^c :
    image of (a+b)/2 is below the middle of the images of a and b
*)

Lemma pow_add_upper : forall a b c, 0<=a -> 0<=b -> 0<c ->
  (a+b)^c <= 2^(pred c) * (a^c + b^c).
Proof.
 assert (aux : forall a b c, 0<=a<=b -> 0<c ->
         (a + b) * (a ^ c + b ^ c) <= 2 * (a * a ^ c + b * b ^ c)).
 (* begin *)
  intros a b c (Ha,H) Hc.
  rewrite !mul_add_distr_l, !mul_add_distr_r. nzsimpl.
  rewrite <- !add_assoc. apply add_le_mono_l.
  rewrite !add_assoc. apply add_le_mono_r.
  destruct (le_exists_sub _ _ H) as (d & EQ & Hd).
  rewrite EQ.
  rewrite 2 mul_add_distr_r.
  rewrite !add_assoc. apply add_le_mono_r.
  rewrite add_comm. apply add_le_mono_l.
  apply mul_le_mono_nonneg_l; trivial.
  apply pow_le_mono_l; try split; order.
 (* end *)
 intros a b c Ha Hb Hc. apply lt_ind with (4:=Hc). solve_predicate_wd.
 nzsimpl; order.
 clear c Hc. intros c Hc IH.
 assert (0<=c) by order.
 nzsimpl; trivial.
 transitivity ((a+b)*(2^(pred c) * (a^c + b^c))).
 apply mul_le_mono_nonneg_l; trivial.
 now apply add_nonneg_nonneg.
 rewrite mul_assoc. rewrite (mul_comm (a+b)).
 assert (EQ : S (P c) == c) by (apply lt_succ_pred with 0; order').
 assert (LE : 0 <= P c) by (now rewrite succ_le_mono, EQ, le_succ_l).
 assert (EQ' : 2^c == 2^(P c) * 2) by (rewrite <- EQ at 1; nzsimpl; order).
 rewrite EQ', <- !mul_assoc.
 apply mul_le_mono_nonneg_l.
 apply pow_nonneg_nonneg; order'.
 destruct (le_gt_cases a b).
 apply aux; try split; order'.
 rewrite (add_comm a), (add_comm (a^c)), (add_comm (a*a^c)).
 apply aux; try split; order'.
Qed.

End NZPowProp.
