(*i $Id $ i*)

(*s Equality is introduced as an independant parameter, it could be 
    instantiated with Leibniz equality *)
Require Export Params.

Parameter eqN:N->N->Prop.  

(*i Infix 6 "=" eqN. i*)

Grammar constr constr1 :=
eq_impl [ constr0($c) "=" constr0($c2) ] -> [ (eqN $c $c2) ].

Syntax constr
  level 1:
    equal [ (eqN $t1 $t2) ] -> [ [<hov 0> $t1:E [0 1]  "=" $t2:E ] ]
.