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
Delimits Scope nat_scope with N.

(* For parsing/printing based on scopes *)
Module nat_scope.

Infix "+" plus (at level 4) : nat_scope.
Infix "*" mult (at level 3): nat_scope.
Infix "<=" le (at level 5, no associativity) : nat_scope.
Infix "<" lt (at level 5, no associativity) : nat_scope.
Infix ">=" ge (at level 5, no associativity) : nat_scope.
Infix ">" gt (at level 5, no associativity) : nat_scope.

(* Warning: this hides sum and prod and breaks sumor symbolic notation *)
Open Scope nat_scope.

(*
Syntax constr
  level 0:
  S' [ (S $p) ] -> [$p:"nat_printer_S":9]
| O' [ O ] -> [ _:"nat_printer_O" ]
.
*)
End nat_scope.
