(*i $Id $ i*)

(*s InEquality is introduced as an independant parameter, it could be 
    instantiated with the negation of equality *)

Require Export Params.

Parameter neq : N -> N -> Prop.

Infix 6 "<>" neq.







