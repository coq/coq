(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of Square Root Function *)

Require Import NAxioms NSub NZSqrt.

Module NSqrtProp (Import A : NAxiomsSig')(Import B : NSubProp A).

 Module Import Private_NZSqrt := Nop <+ NZSqrtProp A A B.

 Ltac auto' := trivial; try rewrite <- neq_0_lt_0; auto using le_0_l.
 Ltac wrap l := intros; apply l; auto'.

 (** We redefine NZSqrt's results, without the non-negative hyps *)

Lemma sqrt_spec' : forall a, √a*√a <= a < S (√a) * S (√a).
Proof. wrap sqrt_spec. Qed.

Definition sqrt_unique : forall a b, b*b<=a<(S b)*(S b) -> √a == b
 := sqrt_unique.

Lemma sqrt_square : forall a, √(a*a) == a.
Proof. wrap sqrt_square. Qed.

Definition sqrt_le_mono : forall a b, a<=b -> √a <= √b
 := sqrt_le_mono.

Definition sqrt_lt_cancel : forall a b, √a < √b -> a < b
 := sqrt_lt_cancel.

Lemma sqrt_le_square : forall a b, b*b<=a <-> b <= √a.
Proof. wrap sqrt_le_square. Qed.

Lemma sqrt_lt_square : forall a b, a<b*b <-> √a < b.
Proof. wrap sqrt_lt_square. Qed.

Definition sqrt_0 := sqrt_0.
Definition sqrt_1 := sqrt_1.
Definition sqrt_2 := sqrt_2.

Definition sqrt_lt_lin : forall a, 1<a -> √a<a
 := sqrt_lt_lin.

Lemma sqrt_le_lin : forall a, √a<=a.
Proof. wrap sqrt_le_lin. Qed.

Definition sqrt_mul_below : forall a b, √a * √b <= √(a*b)
 := sqrt_mul_below.

Lemma sqrt_mul_above : forall a b, √(a*b) < S (√a) * S (√b).
Proof. wrap sqrt_mul_above. Qed.

Lemma sqrt_succ_le : forall a, √(S a) <= S (√a).
Proof. wrap sqrt_succ_le. Qed.

Lemma sqrt_succ_or : forall a, √(S a) == S (√a) \/ √(S a) == √a.
Proof. wrap sqrt_succ_or. Qed.

Definition sqrt_add_le : forall a b, √(a+b) <= √a + √b
 := sqrt_add_le.

Lemma add_sqrt_le : forall a b, √a + √b <= √(2*(a+b)).
Proof. wrap add_sqrt_le. Qed.

(** For the moment, we include stuff about [sqrt_up] with patching them. *)

Include NZSqrtUpProp A A B Private_NZSqrt.

End NSqrtProp.
