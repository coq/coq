(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Attributes deprecated(since="8.20").
Require Export Compare_dec.
Require Export Peano_dec.
Require Import Sumbool.

#[local]
Set Warnings "-deprecated".
Local Open Scope nat_scope.

Implicit Types m n x y : nat.
(** The decidability of equality and order relations over
    type [nat] give some boolean functions with the adequate specification. *)
#[deprecated(since="8.20", note="Use Coq.Arith.Compare_dec.zerop instead")]
Definition notzerop n := sumbool_not _ _ (zerop n).

#[deprecated(since="8.20",
note="Use Arith.Compare_dec.lt_dec and PeanoNat.Nat.nlt_ge instead")]
Definition lt_ge_dec : forall x y, {x < y} + {x >= y} :=
  fun n m => sumbool_not _ _ (le_lt_dec m n).

#[deprecated(since="8.20", note="Use PeanoNat.Nat.ltb instead")]
Definition nat_lt_ge_bool x y := bool_of_sumbool (lt_ge_dec x y).

#[deprecated(since="8.20", note="Use PeanoNat.Nat.leb instead")]
Definition nat_ge_lt_bool x y :=
  bool_of_sumbool (sumbool_not _ _ (lt_ge_dec x y)).

#[deprecated(since="8.20", note="Use PeanoNat.Nat.leb instead")]
Definition nat_le_gt_bool x y := bool_of_sumbool (le_gt_dec x y).

#[deprecated(since="8.20", note="Use PeanoNat.Nat.ltb instead")]
Definition nat_gt_le_bool x y :=
  bool_of_sumbool (sumbool_not _ _ (le_gt_dec x y)).

#[deprecated(since="8.20", note="Use PeanoNat.Nat.eqb instead")]
Definition nat_eq_bool x y := bool_of_sumbool (eq_nat_dec x y).

#[deprecated(since="8.20", note="Use PeanoNat.Nat.eqb instead")]
Definition nat_noteq_bool x y :=
  bool_of_sumbool (sumbool_not _ _ (eq_nat_dec x y)).

#[deprecated(since="8.20", note="Use Coq.Arith.Compare_dec.zerop instead")]
Definition zerop_bool x := bool_of_sumbool (zerop x).

#[deprecated(since="8.20", note="Use Coq.Arith.Compare_dec.zerop instead")]
Definition notzerop_bool x := bool_of_sumbool (notzerop x).
