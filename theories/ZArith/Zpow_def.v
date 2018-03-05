(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinInt Ring_theory.
Local Open Scope Z_scope.

(** * Power functions over [Z] *)

(** Nota : this file is mostly deprecated. The definition of [Z.pow]
    and its usual properties are now provided by module [BinInt.Z]. *)

Notation Zpower_pos := Z.pow_pos (only parsing).
Notation Zpower := Z.pow (only parsing).
Notation Zpower_0_r := Z.pow_0_r (only parsing).
Notation Zpower_succ_r := Z.pow_succ_r (only parsing).
Notation Zpower_neg_r := Z.pow_neg_r (only parsing).
Notation Zpower_Ppow := Pos2Z.inj_pow (only parsing).

Lemma Zpower_theory : power_theory 1 Z.mul (@eq Z) Z.of_N Z.pow.
Proof.
 constructor. intros.
 destruct n;simpl;trivial.
 unfold Z.pow_pos.
 rewrite <- (Z.mul_1_r (pow_pos _ _ _)). generalize 1.
 induction p; simpl; intros; rewrite ?IHp, ?Z.mul_assoc; trivial.
Qed.
