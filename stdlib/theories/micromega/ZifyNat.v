(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Instances of [ZifyClasses] for dealing with advanced [nat] operators. *)

Require Import BinInt Znat Zdiv.
Require Import ZifyClasses ZifyInst Zify.

Ltac zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(** Support for [nat] *)

#[local]
Existing Instance Inj_nat_Z.

#[global]
Instance Op_mod : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp Op_mod.

#[global]
Instance Op_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_div.

#[global]
Instance Op_pow : BinOp Nat.pow :=
  {| TBOp := Z.pow ; TBOpInj := Nat2Z.inj_pow |}.
Add Zify BinOp Op_pow.

#[local] Open Scope Z_scope.

#[global]
Instance SatDiv : Saturate Z.div :=
  {|
    PArg1 := fun x => 0 <= x;
    PArg2 := fun y => 0 <= y;
    PRes  := fun _ _ r => 0 <= r;
    SatOk := Z_div_nonneg_nonneg
  |}.
Add Zify Saturate SatDiv.

#[global]
Instance SatMod : Saturate Z.modulo :=
  {|
    PArg1 := fun x => 0 <= x;
    PArg2 := fun y => 0 <= y;
    PRes  := fun _ _ r => 0 <= r;
    SatOk := Z_mod_nonneg_nonneg
  |}.
Add Zify Saturate SatMod.
