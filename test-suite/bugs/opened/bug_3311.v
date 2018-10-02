Require Import Setoid.
Axiom bar : True = False.
Goal True.
  Fail setoid_rewrite bar. (* Toplevel input, characters 15-33:
Error:
Tactic failure:setoid rewrite failed: Unable to satisfy the rewriting constraints.

Could not find an instance for "subrelation eq (Basics.flip Basics.impl)".
With the following constraints:
?3 : "True" *)
