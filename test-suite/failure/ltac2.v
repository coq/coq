(* Check that Match arguments are forbidden *)
Tactic Definition E x := Apply x.
Goal True->True.
E (Match Context With [ |- ? ] -> Intro H).
(* Should fail with "Immediate Match producing tactics not allowed in 
   local definitions" *)
