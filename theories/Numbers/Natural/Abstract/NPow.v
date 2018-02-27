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

Require Import Bool NAxioms NSub NParity NZPow.

(** Derived properties of power, specialized on natural numbers *)

Module Type NPowProp
 (Import A : NAxiomsSig')
 (Import B : NSubProp A)
 (Import C : NParityProp A B).

 Module Import Private_NZPow := Nop <+ NZPowProp A A B.

Ltac auto' := trivial; try rewrite <- neq_0_lt_0; auto using le_0_l.
Ltac wrap l := intros; apply l; auto'.

Lemma pow_succ_r' : forall a b, a^(S b) == a * a^b.
Proof. wrap pow_succ_r. Qed.

(** Power and basic constants *)

Lemma pow_0_l : forall a, a~=0 -> 0^a == 0.
Proof. wrap pow_0_l. Qed.

Definition pow_1_r : forall a, a^1 == a
 := pow_1_r.

Lemma pow_1_l : forall a, 1^a == 1.
Proof. wrap pow_1_l. Qed.

Definition pow_2_r : forall a, a^2 == a*a
 := pow_2_r.

(** Power and addition, multiplication *)

Lemma pow_add_r : forall a b c, a^(b+c) == a^b * a^c.
Proof. wrap pow_add_r. Qed.

Lemma pow_mul_l : forall a b c, (a*b)^c == a^c * b^c.
Proof. wrap pow_mul_l. Qed.

Lemma pow_mul_r : forall a b c, a^(b*c) == (a^b)^c.
Proof. wrap pow_mul_r. Qed.

(** Power and nullity *)

Lemma pow_eq_0 : forall a b, b~=0 -> a^b == 0 -> a == 0.
Proof. intros. apply (pow_eq_0 a b); trivial. auto'. Qed.

Lemma pow_nonzero : forall a b, a~=0 -> a^b ~= 0.
Proof. wrap pow_nonzero. Qed.

Lemma pow_eq_0_iff : forall a b, a^b == 0 <-> b~=0 /\ a==0.
Proof.
 intros a b. split.
 rewrite pow_eq_0_iff. intros [H |[H H']].
  generalize (le_0_l b); order. split; order.
 intros (Hb,Ha). rewrite Ha. now apply pow_0_l'.
Qed.

(** Monotonicity *)

Lemma pow_lt_mono_l : forall a b c, c~=0 -> a<b -> a^c < b^c.
Proof. wrap pow_lt_mono_l. Qed.

Lemma pow_le_mono_l : forall a b c, a<=b -> a^c <= b^c.
Proof. wrap pow_le_mono_l. Qed.

Lemma pow_gt_1 : forall a b, 1<a -> b~=0 -> 1<a^b.
Proof. wrap pow_gt_1. Qed.

Lemma pow_lt_mono_r : forall a b c, 1<a -> b<c -> a^b < a^c.
Proof. wrap pow_lt_mono_r. Qed.

(** NB: since 0^0 > 0^1, the following result isn't valid with a=0 *)

Lemma pow_le_mono_r : forall a b c, a~=0 -> b<=c -> a^b <= a^c.
Proof. wrap pow_le_mono_r. Qed.

Lemma pow_le_mono : forall a b c d, a~=0 -> a<=c -> b<=d ->
 a^b <= c^d.
Proof. wrap pow_le_mono. Qed.

Definition pow_lt_mono : forall a b c d, 0<a<c -> 0<b<d ->
 a^b < c^d
 := pow_lt_mono.

(** Injectivity *)

Lemma pow_inj_l : forall a b c, c~=0 -> a^c == b^c -> a == b.
Proof. intros; eapply pow_inj_l; eauto; auto'. Qed.

Lemma pow_inj_r : forall a b c, 1<a -> a^b == a^c -> b == c.
Proof. intros; eapply pow_inj_r; eauto; auto'. Qed.

(** Monotonicity results, both ways *)

Lemma pow_lt_mono_l_iff : forall a b c, c~=0 ->
  (a<b <-> a^c < b^c).
Proof. wrap pow_lt_mono_l_iff. Qed.

Lemma pow_le_mono_l_iff : forall a b c, c~=0 ->
  (a<=b <-> a^c <= b^c).
Proof. wrap pow_le_mono_l_iff. Qed.

Lemma pow_lt_mono_r_iff : forall a b c, 1<a ->
  (b<c <-> a^b < a^c).
Proof. wrap pow_lt_mono_r_iff. Qed.

Lemma pow_le_mono_r_iff : forall a b c, 1<a ->
  (b<=c <-> a^b <= a^c).
Proof. wrap pow_le_mono_r_iff. Qed.

(** For any a>1, the a^x function is above the identity function *)

Lemma pow_gt_lin_r : forall a b, 1<a -> b < a^b.
Proof. wrap pow_gt_lin_r. Qed.

(** Someday, we should say something about the full Newton formula.
    In the meantime, we can at least provide some inequalities about
    (a+b)^c.
*)

Lemma pow_add_lower : forall a b c, c~=0 ->
  a^c + b^c <= (a+b)^c.
Proof. wrap pow_add_lower. Qed.

(** This upper bound can also be seen as a convexity proof for x^c :
    image of (a+b)/2 is below the middle of the images of a and b
*)

Lemma pow_add_upper : forall a b c, c~=0 ->
  (a+b)^c <= 2^(pred c) * (a^c + b^c).
Proof. wrap pow_add_upper. Qed.

(** Power and parity *)

Lemma even_pow : forall a b, b~=0 -> even (a^b) = even a.
Proof.
 intros a b Hb. rewrite neq_0_lt_0 in Hb.
 apply lt_ind with (4:=Hb). solve_proper.
 now nzsimpl.
 clear b Hb. intros b Hb IH.
 rewrite pow_succ_r', even_mul, IH. now destruct (even a).
Qed.

Lemma odd_pow : forall a b, b~=0 -> odd (a^b) = odd a.
Proof.
 intros. now rewrite <- !negb_even, even_pow.
Qed.

End NPowProp.
