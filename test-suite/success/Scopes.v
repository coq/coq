(* Check exportation of Argument Scopes even without import of modules *)

Require Import ZArith.

Module A.
Definition opp := Zopp.
End A.
Check (A.opp 3).
