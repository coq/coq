(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Export Le.
Require Export Lt.
Require Export Plus.
Require Export Gt.
Require Export Minus.
Require Export Mult.
Require Export Between.
Require Export Minus.
Require Export Peano_dec.
Require Export Compare_dec.

Axiom My_special_variable : nat -> nat.

Grammar nat number :=.

Grammar constr constr10 :=
  natural_nat [ nat:number($c) ] -> [$c].

Grammar constr pattern :=
  natural_pat [ nat:pat_number($c) ] -> [$c].

Syntax constr
  level  0:
    myspecialvariable [ My_special_variable ] -> ["S"];

  level 10:
  S [ (S $p) ] -> [$p:"nat_printer"]
| O [ O ] -> [ "0" ]
.
