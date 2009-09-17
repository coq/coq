(* Check that no toplevel "unresolved evar" flees through Declare
   Implicit Tactic support (bug #1229) *)

Goal True.
(* should raise an error, not an anomaly *)
set (x := _).
