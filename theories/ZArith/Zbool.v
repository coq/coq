(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require ZArith_base.
Require Sumbool.

(** The decidability of equality and order relations over
    type [Z] give some boolean functions with the adequate specification. *)

Definition Z_lt_ge_bool := [x,y:Z](bool_of_sumbool (Z_lt_ge_dec x y)).
Definition Z_ge_lt_bool := [x,y:Z](bool_of_sumbool (Z_ge_lt_dec x y)).

Definition Z_le_gt_bool := [x,y:Z](bool_of_sumbool (Z_le_gt_dec x y)).
Definition Z_gt_le_bool := [x,y:Z](bool_of_sumbool (Z_gt_le_dec x y)).

Definition Z_eq_bool := [x,y:Z](bool_of_sumbool (Z_eq_dec x y)).
Definition Z_noteq_bool := [x,y:Z](bool_of_sumbool (Z_noteq_dec x y)).

Definition Zeven_odd_bool := [x:Z](bool_of_sumbool (Zeven_odd_dec x)).

