(* This example, checks the efficiency of the abstract machine used by ring *)
(* Expected time < 1.00s *)

Require Import ZArith.
Open Scope Z_scope.
Goal forall a, a+a+a+a+a+a+a+a+a+a+a+a+a = a*13.
Timeout 5 Time intro; ring.
