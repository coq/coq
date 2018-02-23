(* Check exportation of Argument Scopes even without import of modules *)

Require Import ZArith.

Module A.
Definition opp := Z.opp.
End A.
Check (A.opp 3).

(* Test extra scopes to be used in the presence of coercions *)

Record B := { f :> Z -> Z }.
Variable a:B.
Arguments a _%Z_scope : extra scopes.
Check a 0.

(* Check that casts activate scopes if ever possible *)

Inductive U := A.
Bind Scope u with U.
Notation "'ε'" := A : u.
Definition c := ε : U.

(* Check activation of type scope for tactics such as assert *)

Goal True.
assert (nat * nat).

