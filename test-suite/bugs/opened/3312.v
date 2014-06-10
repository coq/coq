Require Import Setoid.
Axiom bar : 0 = 1.
Goal 0 = 1.
  Fail rewrite_strat bar. (* Toplevel input, characters 15-32:
Error: Tactic failure:setoid rewrite failed: Nothing to rewrite. *)
