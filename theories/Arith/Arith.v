
(* $Id$ *)

Require Export Le.
Require Export Lt.
Require Export Plus.
Require Export Gt.
Require Export Minus.
Require Export Mult.
Require Export Between.
Require Export Minus.

Axiom My_special_variable : nat -> nat.

Grammar nat number :=.

Grammar constr constr10 :=
  natural_nat [ nat:number($c) ] -> [$c].

Grammar constr pattern :=
  natural_pat [ nat:number($c) ] -> [$c].

Syntax constr
  level  0:
    myspecialvariable [ My_special_variable ] -> ["S"];

  level 10:
  S [ (S $p) ] -> [$p:"nat_printer"]
| O [ O ] -> [ "0" ]
.
