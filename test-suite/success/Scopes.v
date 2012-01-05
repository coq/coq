(* Check exportation of Argument Scopes even without import of modules *)

Require Import ZArith.

Module A.
Definition opp := Zopp.
End A.
Check (A.opp 3).

(* Test extra scopes to be used in the presence of coercions *)

Record B := { f :> Z -> Z }.
Variable a:B.
Arguments Scope a [Z_scope].
Check a 0.
