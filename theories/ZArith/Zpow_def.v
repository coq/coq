(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt Ring_theory.
Local Open Scope Z_scope.

(** * Power functions over [Z] *)

(** Nota : this file is mostly deprecated. The definition of [Z.pow]
    and its usual properties are now provided by module [BinInt.Z]. *)

Notation Zpower_pos := Z.pow_pos (compat "8.3").
Notation Zpower := Z.pow (compat "8.3").
Notation Zpower_0_r := Z.pow_0_r (compat "8.3").
Notation Zpower_succ_r := Z.pow_succ_r (compat "8.3").
Notation Zpower_neg_r := Z.pow_neg_r (compat "8.3").
Notation Zpower_Ppow := Pos2Z.inj_pow (compat "8.3").

Lemma Zpower_theory : power_theory 1 Z.mul (@eq Z) Z.of_N Z.pow.
Proof.
 constructor. intros.
 destruct n;simpl;trivial.
 unfold Z.pow_pos.
 rewrite <- (Z.mul_1_r (pow_pos _ _ _)). generalize 1.
 induction p; simpl; intros; rewrite ?IHp, ?Z.mul_assoc; trivial.
Qed.
