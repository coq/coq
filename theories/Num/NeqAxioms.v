(*i $Id $ i*)

(*s InEquality is introduced as an independant parameter, it could be 
    instantiated with the negation of equality *)

Require Export EqParams.
Require Export NeqParams.

Axiom eq_not_neq : (x,y:N)x=y->~(x<>y).
Hints Immediate eq_not_neq : num.

Axiom neq_sym : (x,y:N)(x<>y)->(y<>x).
Hints Resolve neq_sym : num.

Axiom neq_not_neq_trans : (x,y,z:N)(x<>y)->~(y<>z)->(x<>z).
Hints Resolve neq_not_neq_trans : num.









