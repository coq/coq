(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Arith_prebase.

Require Export Le.
Require Export Lt.
Require Export Plus.
Require Export Gt.
Require Export Minus.
Require Export Mult.

Require Export Factorial.
Require Export Between.
Require Export Peano_dec.
Require Export Compare_dec.
Require Export EqNat.
Require Export Wf_nat.

(* ** [eq_nat] *)
#[global]
Hint Resolve eq_nat_refl: arith.
#[global]
Hint Immediate eq_eq_nat eq_nat_eq: arith.

(* ** [between] *)
#[global]
Hint Resolve nth_O bet_S bet_emp bet_eq between_Sk_l exists_S exists_le
  in_int_S in_int_intro: arith.
#[global]
Hint Immediate in_int_Sp_q exists_le_S exists_S_le: arith.
