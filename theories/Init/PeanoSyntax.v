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

V7only[
Syntax constr
  level 0:
    S [ (S $p) ] -> [$p:"nat_printer":9]
  | O [ O ]      -> ["(0)"].
].
(* Outside the module to be able to parse the grammar for 0,1,2... !! *)
Delimits Scope nat_scope with N.

(* For parsing/printing based on scopes *)
Module nat_scope.

(* Warning: this hides sum and prod and breaks sumor symbolic notation *)
Open Scope nat_scope.

Infix 4 "+" plus : nat_scope V8only (left associativity).
Infix 4 "-" minus : nat_scope V8only (left associativity).
Infix 3 "*" mult : nat_scope V8only (left associativity).
Infix NONA 5 "<=" le : nat_scope.
Infix NONA 5 "<" lt : nat_scope.
Infix NONA 5 ">=" ge : nat_scope.
Infix NONA 5 ">" gt : nat_scope.

End nat_scope.
