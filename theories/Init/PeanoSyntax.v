(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*i 	$Id$ *)

Require Datatypes.
Require Peano.

Syntax constr
  level 0:
    S [ (S $p) ] -> [$p:"nat_printer"]
  | O [ O ]      -> ["(0)"].

(* Outside the module to be able to parse the grammar for 0,1,2... !! *)
Delimiters "'N:" nat_scope "'". (* "[N", "[N:", "]]" are conflicting *)

(* For parsing/printing based on scopes *)
Module nat_scope.

Infix LEFTA 4 "+" plus : nat_scope.
Infix LEFTA 3 "*" mult : nat_scope.
Infix 5 "<=" le : nat_scope.
Infix 5 "<" lt : nat_scope.
Infix 5 ">=" ge : nat_scope.
(* Infix 5 ">" gt : nat_scope. (* Conflicts with "<..>Cases ... " *) *)

(* Warning: this hides sum and prod and breaks sumor symbolic notation *)
Open Scope nat_scope.

Syntax constr
  level 0:
  S' [ (S $p) ] -> [$p:"nat_printer_S":9]
| O' [ O ] -> [ _:"nat_printer_O" ]
.

End nat_scope.
