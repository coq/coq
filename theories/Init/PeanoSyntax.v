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

(* This conflicts with expressions like "(0+x)" ...
Grammar nat number :=.

Grammar constr constr0 :=
  natural_nat [ "(" nat:number($c) ")" ] -> [$c].

Grammar constr pattern :=
  natural_pat [ "(" nat:pat_number($c) ")" ] -> [$c].
*)

Syntax constr
  level 10:
  S [ (S $p) ] -> [$p:"nat_printer":9]
| O [ O ] -> [ "0" ]
.


(* Outside the module to be able to parse the grammar for 0,1,2... !! *)
Delimiters "'N:" nat_scope "'". (* "[N", "[N:", "]]" are conflicting *)

(* For parsing/printing based on scopes *)
Module nat_scope.

Infix 3 "+" plus : nat_scope.
Infix 2 "*" mult : nat_scope.
Infix NONA 4 "<=" le : nat_scope.
Infix NONA 4 "<" lt : nat_scope.
Infix NONA 4 ">=" ge : nat_scope.
(* Infix 4 ">" gt : nat_scope. (* Conflicts with "<..>Cases ... " *) *)

(* Warning: this hides sum and prod and breaks sumor symbolic notation *)
Open Scope nat_scope.

Syntax constr
  level 0:
  S' [ (S $p) ] -> [$p:"nat_printer_S":9]
| O' [ O ] -> [ _:"nat_printer_O" ]
.

End nat_scope.

Grammar constr constr0 :=
  natural_nat0 [ "(" "0" ")" ] -> [ 'N: 0 ' ]
| natural_nat1 [ "(" "1" ")" ] -> [ 'N: 1 ' ]
| natural_nat2 [ "(" "2" ")" ] -> [ 'N: 2 ' ]
| natural_nat3 [ "(" "3" ")" ] -> [ 'N: 3 ' ]
| natural_nat4 [ "(" "4" ")" ] -> [ 'N: 4 ' ]
| natural_nat5 [ "(" "5" ")" ] -> [ 'N: 5 ' ]
| natural_nat6 [ "(" "6" ")" ] -> [ 'N: 6 ' ]
| natural_nat7 [ "(" "7" ")" ] -> [ 'N: 7 ' ]
| natural_nat8 [ "(" "8" ")" ] -> [ 'N: 8 ' ]
| natural_nat9 [ "(" "9" ")" ] -> [ 'N: 9 ' ]
| natural_nat10 [ "(" "10" ")" ] -> [ 'N: 10 ' ]
| natural_nat11 [ "(" "11" ")" ] -> [ 'N: 11 ' ]
.

Grammar constr pattern :=
  natural_pat0 [ "(" "0" ")" ] -> [ 'N: 0 ' ]
| natural_pat1 [ "(" "1" ")" ] -> [ 'N: 1 ' ]
| natural_pat2 [ "(" "2" ")" ] -> [ 'N: 2 ' ]
| natural_pat3 [ "(" "3" ")" ] -> [ 'N: 3 ' ]
| natural_pat4 [ "(" "4" ")" ] -> [ 'N: 4 ' ]
| natural_pat5 [ "(" "5" ")" ] -> [ 'N: 5 ' ]
| natural_pat6 [ "(" "6" ")" ] -> [ 'N: 6 ' ]
| natural_pat7 [ "(" "7" ")" ] -> [ 'N: 7 ' ]
| natural_pat8 [ "(" "8" ")" ] -> [ 'N: 8 ' ]
| natural_pat9 [ "(" "9" ")" ] -> [ 'N: 9 ' ]
| natural_pat10 [ "(" "10" ")" ] -> [ 'N: 10 ' ]
| natural_pat11 [ "(" "11" ")" ] -> [ 'N: 11 ' ]
.
