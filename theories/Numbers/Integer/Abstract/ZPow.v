(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of the power function *)

Require Import Bool ZAxioms ZMulOrder ZParity ZSgnAbs NZPow.

Module Type ZPowProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZParityProp A B)
 (Import D : ZSgnAbsProp A B).

 Include NZPowProp A A B.

(** A particular case of [pow_add_r], with no precondition *)

Lemma pow_twice_r a b : a^(2*b) == a^b * a^b.
Proof.
 rewrite two_succ. nzsimpl.
 destruct (le_gt_cases 0 b).
 - now rewrite pow_add_r.
 - rewrite !pow_neg_r. now nzsimpl. trivial.
   now apply add_neg_neg.
Qed.

(** Parity of power *)

Lemma even_pow : forall a b, 0<b -> even (a^b) = even a.
Proof.
 intros a b Hb. apply lt_ind with (4:=Hb). solve_proper.
 now nzsimpl.
 clear b Hb. intros b Hb IH. nzsimpl; [|order].
 rewrite even_mul, IH. now destruct (even a).
Qed.

Lemma odd_pow : forall a b, 0<b -> odd (a^b) = odd a.
Proof.
 intros. now rewrite <- !negb_even, even_pow.
Qed.

(** Properties of power of negative numbers *)

Lemma pow_opp_even : forall a b, Even b -> (-a)^b == a^b.
Proof.
 intros a b (c,H). rewrite H.
 destruct (le_gt_cases 0 c).
 rewrite 2 pow_mul_r by order'.
 rewrite 2 pow_2_r.
 now rewrite mul_opp_opp.
 assert (2*c < 0) by (apply mul_pos_neg; order').
 now rewrite !pow_neg_r.
Qed.

Lemma pow_opp_odd : forall a b, Odd b -> (-a)^b == -(a^b).
Proof.
 intros a b (c,H). rewrite H.
 destruct (le_gt_cases 0 c) as [LE|GT].
 assert (0 <= 2*c) by (apply mul_nonneg_nonneg; order').
 rewrite add_1_r, !pow_succ_r; trivial.
 rewrite pow_opp_even by (now exists c).
 apply mul_opp_l.
 apply double_above in GT. rewrite mul_0_r in GT.
 rewrite !pow_neg_r by trivial. now rewrite opp_0.
Qed.

Lemma pow_even_abs : forall a b, Even b -> a^b == (abs a)^b.
Proof.
 intros. destruct (abs_eq_or_opp a) as [EQ|EQ]; rewrite EQ.
 reflexivity.
 symmetry. now apply pow_opp_even.
Qed.

Lemma pow_even_nonneg : forall a b, Even b -> 0 <= a^b.
Proof.
 intros. rewrite pow_even_abs by trivial.
 apply pow_nonneg, abs_nonneg.
Qed.

Lemma pow_odd_abs_sgn : forall a b, Odd b -> a^b == sgn a * (abs a)^b.
Proof.
 intros a b H.
 destruct (sgn_spec a) as [(LT,EQ)|[(EQ',EQ)|(LT,EQ)]]; rewrite EQ.
 nzsimpl.
 rewrite abs_eq; order.
 rewrite <- EQ'. nzsimpl.
 destruct (le_gt_cases 0 b).
 apply pow_0_l.
 assert (b~=0) by (contradict H; now rewrite H, <-odd_spec, odd_0).
 order.
 now rewrite pow_neg_r.
 rewrite abs_neq by order.
 rewrite pow_opp_odd; trivial.
 now rewrite mul_opp_opp, mul_1_l.
Qed.

Lemma pow_odd_sgn : forall a b, 0<=b -> Odd b -> sgn (a^b) == sgn a.
Proof.
 intros a b Hb H.
 destruct (sgn_spec a) as [(LT,EQ)|[(EQ',EQ)|(LT,EQ)]]; rewrite EQ.
 apply sgn_pos. apply pow_pos_nonneg; trivial.
 rewrite <- EQ'. rewrite pow_0_l. apply sgn_0.
 assert (b~=0) by (contradict H; now rewrite H, <-odd_spec, odd_0).
 order.
 apply sgn_neg.
 rewrite <- (opp_involutive a). rewrite pow_opp_odd by trivial.
 apply opp_neg_pos.
 apply pow_pos_nonneg; trivial.
 now apply opp_pos_neg.
Qed.

Lemma abs_pow : forall a b, abs (a^b) == (abs a)^b.
Proof.
 intros a b.
 destruct (Even_or_Odd b).
 rewrite pow_even_abs by trivial.
 apply abs_eq, pow_nonneg, abs_nonneg.
 rewrite pow_odd_abs_sgn by trivial.
 rewrite abs_mul.
 destruct (lt_trichotomy 0 a) as [Ha|[Ha|Ha]].
 rewrite (sgn_pos a), (abs_eq 1), mul_1_l by order'.
 apply abs_eq, pow_nonneg, abs_nonneg.
 rewrite <- Ha, sgn_0, abs_0, mul_0_l.
 symmetry. apply pow_0_l'. intro Hb. rewrite Hb in H.
 apply (Even_Odd_False 0); trivial. exists 0; now nzsimpl.
 rewrite (sgn_neg a), abs_opp, (abs_eq 1), mul_1_l by order'.
 apply abs_eq, pow_nonneg, abs_nonneg.
Qed.

End ZPowProp.
