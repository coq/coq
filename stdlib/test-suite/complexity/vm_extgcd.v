(* Euclidian algorithm defined by fuel-assisted well-founded recrsion on Z *)
(* Expected time < 1.00s *)

From Stdlib Require Import ZArith Znumtheory. Local Open Scope Z_scope.
Goal True.
  Time
  let x := constr:(let '(a,b,c) := extgcd 2 (2^19937-1) in Z.odd (a+b+c)) in
  let y := eval vm_compute in x in
  first [constr_eq y true | constr_eq y false].
Abort.
