
(*s Definition of inequality *)

Require Params.
Require EqParams.
Definition neq [x,y:N] := (eqN x y)->False.

Infix 6 "<>" neq.

