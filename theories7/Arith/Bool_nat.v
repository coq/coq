(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Export Compare_dec.
Require Export Peano_dec.
Require Sumbool.

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n,x,y:nat.

(** The decidability of equality and order relations over
    type [nat] give some boolean functions with the adequate specification. *)

Definition notzerop := [n:nat] (sumbool_not ? ? (zerop n)).
Definition lt_ge_dec : (x,y:nat){(lt x y)}+{(ge x y)} := 
  [n,m:nat] (sumbool_not ? ? (le_lt_dec m n)).

Definition nat_lt_ge_bool := 
  [x,y:nat](bool_of_sumbool (lt_ge_dec x y)).
Definition nat_ge_lt_bool := 
  [x,y:nat](bool_of_sumbool (sumbool_not ? ? (lt_ge_dec x y))).

Definition nat_le_gt_bool := 
  [x,y:nat](bool_of_sumbool (le_gt_dec x y)).
Definition nat_gt_le_bool := 
  [x,y:nat](bool_of_sumbool (sumbool_not ? ? (le_gt_dec x y))).

Definition nat_eq_bool :=
  [x,y:nat](bool_of_sumbool (eq_nat_dec x y)).
Definition nat_noteq_bool := 
  [x,y:nat](bool_of_sumbool (sumbool_not ? ? (eq_nat_dec x y))).

Definition zerop_bool := [x:nat](bool_of_sumbool (zerop x)).
Definition notzerop_bool := [x:nat](bool_of_sumbool (notzerop x)).
