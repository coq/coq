(* The extended euclidian algorithm implementation is kinda slow *)
(* Expected time < 1.00s *)

Require Import ZArith Znumtheory. Local Open Scope Z_scope.
Goal True.
  let x := constr:(let (u, v, d, _,  _) := euclid 2 65521 in (u,v,d)) in
  let y := eval vm_compute in x in
  lazymatch y with pair _ _ => idtac end;
  pose y.
Abort.
